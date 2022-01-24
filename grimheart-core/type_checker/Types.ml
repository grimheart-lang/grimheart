open Core_kernel
open Grimheart_ast
open Grimheart_core_errors
open Grimheart_core_errors.Let

let fresh_name : unit -> string =
  let i = ref (-1) in
  fun () ->
    incr i;
    "t" ^ string_of_int !i

let insert_in_between ((gammaL, gammaR) : Context.t * Context.t)
    ((a, a', b') : string * string * string) (ctor : Type.t -> Type.t -> Type.t)
    : Context.t =
  let gammaM : Context.t =
    [Solved (a, ctor (Unsolved a') (Unsolved b')); Unsolved a'; Unsolved b']
  in
  List.concat [gammaL; gammaM; gammaR]

module type S = sig
  val subsumes :
    Context.t -> Type.t -> Type.t -> (Context.t, Grimheart_core_errors.t) result

  val unify :
    Context.t -> Type.t -> Type.t -> (Context.t, Grimheart_core_errors.t) result

  val solve :
    Context.t -> string -> Type.t -> (Context.t, Grimheart_core_errors.t) result

  val check :
       Context.t
    -> unit Expr.t
    -> Type.t
    -> (Context.t, Grimheart_core_errors.t) result

  val infer :
       Context.t
    -> unit Expr.t
    -> (Context.t * Type.t, Grimheart_core_errors.t) result

  val infer_apply :
       Context.t
    -> Type.t
    -> unit Expr.t
    -> (Context.t * Type.t, Grimheart_core_errors.t) result

  val infer_type_with :
    Context.t -> unit Expr.t -> (Type.t, Grimheart_core_errors.t) result

  val infer_type : unit Expr.t -> (Type.t, Grimheart_core_errors.t) result
end

module Make (Env : Grimheart_core_environment.S) (Kinds : Kinds.S) : S = struct
  open Env
  open Type.Primitives

  let rec subsumes (gamma : Context.t) (t1 : Type.t) (t2 : Type.t) :
      Context.t result' =
    with_hint (SubsumingTypes (t1, t2))
    @@
    match (t1, t2) with
    | Apply (Apply (t_function1, a1), b1), Apply (Apply (t_function2, a2), b2)
      when Type.equal t_function t_function1
           && Type.equal t_function t_function2 ->
        let* theta = unify gamma a2 a1 in
        unify theta (Context.apply theta b1) (Context.apply theta b2)
    | _, Forall (b, k2, t2) ->
        let b' = fresh_name () in
        let t2 = Type.substitute b (Skolem (b', k2)) t2 in
        Context.scoped gamma (Quantified b') (fun gamma -> subsumes gamma t1 t2)
    | Forall (a, _, t1), _ ->
        let a' = fresh_name () in
        let t1 = Type.substitute a (Unsolved a') t1 in
        Context.scoped_unsolved gamma a' (fun gamma -> subsumes gamma t1 t2)
    | _ -> unify gamma t1 t2

  and unify (gamma : Context.t) (t1 : Type.t) (t2 : Type.t) : Context.t result'
      =
    with_hint (UnifyingTypes (t1, t2))
    @@
    match (t1, t2) with
    | Constructor a, Constructor b when String.equal a b ->
        (* todo: perform environment checks here? *)
        Ok gamma
    | (Skolem (a, _), Skolem (b, _) | Variable a, Variable b)
      when String.equal a b ->
        (* `a` must exist within the context *)
        let* _ = Context.well_formed_type gamma t1 in
        Ok gamma
    (* we only need these variables to be unsolved *)
    | Unsolved a, Unsolved b
      when String.equal a b && Context.mem gamma (Unsolved a) ->
        Ok gamma
    | Forall (a1, k1, t1), Forall (a2, k2, t2) ->
        let a' = fresh_name () in
        let t1 = Type.substitute a1 (Skolem (a', k1)) t1 in
        let t2 = Type.substitute a2 (Skolem (a', k2)) t2 in
        Context.scoped gamma (Quantified a') (fun gamma -> unify gamma t1 t2)
    | _, Forall (b, k2, t2) ->
        let b' = fresh_name () in
        let t2 = Type.substitute b (Skolem (b', k2)) t2 in
        Context.scoped gamma (Quantified b') (fun gamma -> unify gamma t1 t2)
    | Forall (a, k1, t1), _ ->
        let a' = fresh_name () in
        let t1 = Type.substitute a (Skolem (a', k1)) t1 in
        Context.scoped gamma (Quantified a') (fun gamma -> unify gamma t1 t2)
    | Unsolved a, _
      when Context.mem gamma (Unsolved a)
           && not (Set.mem (Type.free_type_variables t2) a) ->
        solve gamma a t2
    | _, Unsolved b
      when Context.mem gamma (Unsolved b)
           && not (Set.mem (Type.free_type_variables t1) b) ->
        solve gamma b t1
    | Apply (a1, b1), Apply (a2, b2) ->
        let* gamma = unify gamma a1 a2 in
        unify gamma b1 b2
    | KindApply (a1, b1), KindApply (a2, b2) ->
        let* gamma = Kinds.unify gamma a1 a2 in
        unify gamma b1 b2
    | _U, Annotate (_T, _K) ->
        let* gamma, _ = Kinds.check gamma _U _K in
        unify gamma _U _T
    | Annotate (_T, _K), _U ->
        let* gamma, _ = Kinds.check gamma _U _K in
        unify gamma _T _U
    | _ -> Error (with_message (CouldNotUnifyTypes (t1, t2)))

  and solve (gamma : Context.t) (a : string) (_B : Type.t) : Context.t result' =
    let* (gammaL, gammaR) : Context.t * Context.t =
      Context.break_apart_at_unsolved a gamma
    in
    let insertSolved (t : Type.t) : Context.t result' =
      let* _ = Context.well_formed_type gammaR _B in
      Ok (List.append gammaL (Solved (a, t) :: gammaR))
    in
    match _B with
    | Constructor _ -> insertSolved _B
    | Variable _ -> insertSolved _B
    | Skolem _ -> insertSolved _B
    | Unsolved b -> (
        match Context.break_apart_at_unsolved b gammaL with
        | Error _ -> insertSolved _B
        | Ok (gammaLL, gammaLR) ->
            let gammaL =
              List.append gammaLL (Solved (b, Unsolved a) :: gammaLR)
            in
            let gamma = List.append gammaL (Unsolved a :: gammaR) in
            Ok gamma)
    | Apply (Apply (t_function', _A), _B) when Type.equal t_function t_function'
      ->
        let a' = fresh_name () in
        let b' = fresh_name () in
        let gamma =
          insert_in_between (gammaL, gammaR) (a, a', b') Type.Sugar.fn
        in
        let* theta = solve gamma a' _A in
        solve theta b' (Context.apply theta _B)
    | Forall (b, _, _B) ->
        Context.scoped gamma (Quantified b) (fun gamma -> solve gamma a _B)
    | Apply (_A, _B) ->
        let a' = fresh_name () in
        let b' = fresh_name () in
        let gamma =
          insert_in_between (gammaL, gammaR) (a, a', b') Type.Sugar.ap
        in
        let* theta = solve gamma a' _A in
        solve theta b' (Context.apply theta _B)
    | KindApply (_A, _B) ->
        let a' = fresh_name () in
        let b' = fresh_name () in
        let gamma =
          insert_in_between (gammaL, gammaR) (a, a', b') Type.Sugar.k_ap
        in
        let* theta = solve gamma a' _A in
        solve theta b' (Context.apply theta _B)
    | Annotate (_A, _B) ->
        let a' = fresh_name () in
        let b' = fresh_name () in
        let gamma =
          insert_in_between (gammaL, gammaR) (a, a', b') Type.Sugar.an
        in
        let* theta = solve gamma a' _A in
        solve theta b' (Context.apply theta _B)

  and check (gamma : Context.t) (e : _ Expr.t) (_A : Type.t) : Context.t result'
      =
    with_hint (CheckingType (e, _A))
    @@
    match (e, _A) with
    | Literal (Char _), Constructor "Char"
    | Literal (String _), Constructor "String"
    | Literal (Int _), Constructor "Int"
    | Literal (Float _), Constructor "Float" ->
        Ok gamma
    | Literal (Array _As), Apply (Constructor "Array", _A') ->
        let rec aux gamma = function
          | h :: t ->
              let* gamma = check gamma h _A' in
              aux gamma t
          | [] -> Ok gamma
        in
        aux gamma _As
    | Literal (Object _), _ ->
        raise
          (Failure "todo: checking routine for object is not yet implemented")
    | Lambda (n, e), Apply (Apply (t_function', ar), re)
      when Type.equal t_function t_function' ->
        let n' = fresh_name () in
        Names.bracketed (fun () ->
            Names.set n' ar;
            check gamma (Expr.substitute n (Variable n') e) re)
    | _, Forall (a, k, _A) ->
        let a' = fresh_name () in
        let _A = Type.substitute a (Skolem (a', k)) _A in
        Context.scoped gamma (Quantified a') (fun gamma -> check gamma e _A)
    | _ ->
        let* theta, _A' = infer gamma e in
        subsumes theta (Context.apply theta _A') (Context.apply theta _A)

  and infer (gamma : Context.t) (e : _ Expr.t) : (Context.t * Type.t) result' =
    with_hint (InferringType e)
    @@
    match e with
    | Literal (Char _) -> Ok (gamma, t_char)
    | Literal (String _) -> Ok (gamma, t_string)
    | Literal (Int _) -> Ok (gamma, t_int)
    | Literal (Float _) -> Ok (gamma, t_float)
    | Literal (Array _As) ->
        let a = fresh_name () in
        let rec aux (gamma : Context.t) (current_t : Type.t option) :
            _ -> (Context.t * Type.t) result' = function
          | h :: t -> (
              let* gamma, inferred_t = infer gamma h in
              match (inferred_t, current_t) with
              | _, Some current_t ->
                  (* todo: make this rethrow a better error *)
                  let* gamma = unify gamma inferred_t current_t in
                  aux gamma (Some inferred_t) t
              | _, None -> aux gamma (Some inferred_t) t)
          | [] -> (
              (* NOTE: These annotations propagate up but they aren't erased at
                 any point by the top-level generalization algorithm. As such,
                 tests would have to explicitly look for annotations... for
                 now. *)
              match current_t with
              | Some current_t -> Ok (gamma, Apply (t_array, current_t))
              | None -> Ok (Unsolved a :: gamma, Apply (t_array, Unsolved a)))
        in
        aux gamma None _As
    | Literal (Object _) ->
        raise
          (Failure "todo: inference routine for object is not yet implemented")
    | Variable v -> (
        match Names.find v with
        | Some t -> Ok (gamma, t)
        | None -> Error (with_message (UnknownVariable v)))
    | Lambda (v, e) ->
        let a' = fresh_name () in
        let b' = fresh_name () in
        let* delta =
          let v' = fresh_name () in
          Names.bracketed (fun () ->
              Names.set v' (Unsolved a');
              Context.scoped (Unsolved b' :: Unsolved a' :: gamma) (Marker v')
                (fun gamma ->
                  check gamma (Expr.substitute v (Variable v') e) (Unsolved b')))
        in
        Ok (delta, Type.Sugar.fn (Unsolved a') (Unsolved b'))
    | Apply (f, x) ->
        let* theta, t = infer gamma f in
        infer_apply theta (Context.apply theta t) x
    | Annotate (e, t) ->
        let* theta = check gamma e t in
        Ok (theta, t)
    | Let (v, t, e1, e2) ->
        let* gamma, t =
          match t with
          | Some t ->
              let* gamma = check gamma e1 t in
              Ok (gamma, t)
          | None -> infer gamma e1
        in
        let v' = fresh_name () in
        Names.bracketed (fun () ->
            Names.set v' t;
            infer gamma (Expr.substitute v (Variable v') e2))

  and infer_apply (gamma : Context.t) (_A : Type.t) (e : _ Expr.t) :
      (Context.t * Type.t) result' =
    match _A with
    | Forall (a, _K, _A) ->
        let a' = fresh_name () in
        let _A = Type.substitute a (Unsolved a') _A in
        infer_apply (Unsolved a' :: gamma) _A e
    | Unsolved a ->
        let a' = fresh_name () in
        let b' = fresh_name () in
        let* gammaL, gammaR = Context.break_apart_at_unsolved a' gamma in
        let gamma =
          insert_in_between (gammaL, gammaR) (a, a', b') Type.Sugar.fn
        in
        let* delta = check gamma e (Unsolved a') in
        Ok (delta, Type.Unsolved b')
    | Apply (Apply (t_function', _A), _B) when Type.equal t_function t_function'
      ->
        let* delta = check gamma e _A in
        Ok (delta, _B)
    | _ -> Error (with_message (CouldNotApplyTypeOn (_A, e)))

  let infer_type_with (context : Context.t) (e : _ Expr.t) : Type.t result' =
    let* delta, poly_type = infer context e in
    let fresh_variable =
      let i = ref (-1) in
      fun () ->
        incr i;
        String.of_char (Char.of_int_exn (97 + (!i mod 26)))
    in
    let algebra (element : Context.Element.t) (poly_type : Type.t) : Type.t =
      match element with
      | Unsolved u when Set.mem (Type.free_type_variables poly_type) u ->
          let u' = fresh_variable () in
          Forall (u', None, Type.substitute u (Variable u') poly_type)
      | _ -> poly_type
    in
    Ok (List.fold_right delta ~f:algebra ~init:(Context.apply delta poly_type))

  let infer_type : _ Expr.t -> Type.t result' = infer_type_with []
end
