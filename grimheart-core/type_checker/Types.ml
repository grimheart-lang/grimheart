open Core_kernel
open Grimheart_ast
open Grimheart_errors
open Grimheart_errors.Let

module type S = sig
  val subsumes :
    Context.t -> Type.t -> Type.t -> (Context.t, Grimheart_errors.t) result

  val unify :
    Context.t -> Type.t -> Type.t -> (Context.t, Grimheart_errors.t) result

  val solve :
    Context.t -> string -> Type.t -> (Context.t, Grimheart_errors.t) result

  val check :
    Context.t -> unit Expr.t -> Type.t -> (Context.t, Grimheart_errors.t) result

  val infer :
    Context.t -> unit Expr.t -> (Context.t * Type.t, Grimheart_errors.t) result

  val infer_apply :
       Context.t
    -> Type.t
    -> unit Expr.t
    -> (Context.t * Type.t, Grimheart_errors.t) result

  val infer_type_with :
    Context.t -> unit Expr.t -> (Type.t, Grimheart_errors.t) result

  val infer_type : unit Expr.t -> (Type.t, Grimheart_errors.t) result
end

module Make (Env : Grimheart_environment.S) (Kinds : Kinds.S) : S = struct
  open Type.Primitives

  let fresh_name : unit -> string =
    let i = ref (-1) in
    fun () ->
      incr i;
      "t" ^ string_of_int !i

  let insert_in_between ((gammaL, gammaR) : Context.t * Context.t)
      ((a, a', b') : string * string * string)
      (ctor : Type.t -> Type.t -> Type.t) : Context.t =
    let gammaM : Context.t =
      [Solved (a, ctor (Unsolved a') (Unsolved b')); Unsolved a'; Unsolved b']
    in
    List.concat [gammaL; gammaM; gammaR]

  let rec subsumes (gamma : Context.t) (t1 : Type.t) (t2 : Type.t) :
      (Context.t, Grimheart_errors.t) result =
    with_hint (SubsumingTypes (t1, t2))
    @@
    match (t1, t2) with
    | Apply (Apply (t_function1, a1), b1), Apply (Apply (t_function2, a2), b2)
      when Type.equal t_function t_function1
           && Type.equal t_function t_function2 ->
        let* theta = subsumes gamma a2 a1 in
        subsumes theta (Context.apply theta b1) (Context.apply theta b2)
    | _, Forall (b, k2, t2) ->
        let b' = fresh_name () in
        let t2 = Type.substitute b (Skolem (b', k2)) t2 in
        Context.scoped gamma (Quantified b') (fun gamma -> subsumes gamma t1 t2)
    | Forall (a, _, t1), _ ->
        let a' = fresh_name () in
        let t1 = Type.substitute a (Unsolved a') t1 in
        Context.scoped_unsolved gamma a' (fun gamma -> subsumes gamma t1 t2)
    | _ -> unify gamma t1 t2

  and unify (gamma : Context.t) (t1 : Type.t) (t2 : Type.t) :
      (Context.t, Grimheart_errors.t) result =
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
    | _, Annotate (t, k) ->
        let* gamma, _ = Kinds.check gamma t k in
        unify gamma t1 t
    | Annotate (t, k), _ ->
        let* gamma, _ = Kinds.check gamma t k in
        unify gamma t t2
    | _ -> Error (with_message (CouldNotUnifyTypes (t1, t2)))

  and solve (gamma : Context.t) (a : string) (t : Type.t) :
      (Context.t, Grimheart_errors.t) result =
    let* (gammaL, gammaR) : Context.t * Context.t =
      Context.break_apart_at_unsolved a gamma
    in
    let insertSolved (t : Type.t) : (Context.t, Grimheart_errors.t) result =
      let* _ = Context.well_formed_type gammaR t in
      Ok (List.append gammaL (Solved (a, t) :: gammaR))
    in
    match t with
    | Constructor _ -> insertSolved t
    | Variable _ -> insertSolved t
    | Skolem _ -> insertSolved t
    | Unsolved b -> (
        match Context.break_apart_at_unsolved b gammaL with
        | Error _ -> insertSolved t
        | Ok (gammaLL, gammaLR) ->
            let gammaL =
              List.append gammaLL (Solved (b, Unsolved a) :: gammaLR)
            in
            let gamma = List.append gammaL (Unsolved a :: gammaR) in
            Ok gamma)
    | Apply (Apply (t_function', i), o) when Type.equal t_function t_function'
      ->
        let a' = fresh_name () in
        let b' = fresh_name () in
        let gamma =
          insert_in_between (gammaL, gammaR) (a, a', b') Type.Sugar.fn
        in
        let* theta = solve gamma a' i in
        solve theta b' (Context.apply theta o)
    | Forall (b, _, t) ->
        Context.scoped gamma (Quantified b) (fun gamma -> solve gamma a t)
    | Apply (f, x) ->
        let a' = fresh_name () in
        let b' = fresh_name () in
        let gamma =
          insert_in_between (gammaL, gammaR) (a, a', b') Type.Sugar.ap
        in
        let* theta = solve gamma a' f in
        solve theta b' (Context.apply theta x)
    | KindApply (f, x) ->
        let a' = fresh_name () in
        let b' = fresh_name () in
        let gamma =
          insert_in_between (gammaL, gammaR) (a, a', b') Type.Sugar.k_ap
        in
        let* theta = solve gamma a' f in
        solve theta b' (Context.apply theta x)
    | Annotate (t, k) ->
        let a' = fresh_name () in
        let b' = fresh_name () in
        let gamma =
          insert_in_between (gammaL, gammaR) (a, a', b') Type.Sugar.an
        in
        let* theta = solve gamma a' t in
        solve theta b' (Context.apply theta k)

  and check (gamma : Context.t) (e : _ Expr.t) (t : Type.t) :
      (Context.t, Grimheart_errors.t) result =
    with_hint (CheckingType (e, t))
    @@
    match (e, t) with
    | Literal (Char _), Constructor "Char"
    | Literal (String _), Constructor "String"
    | Literal (Int _), Constructor "Int"
    | Literal (Float _), Constructor "Float" ->
        Ok gamma
    | Literal (Array ts), Apply (Constructor "Array", t) ->
        let rec aux gamma = function
          | h :: rest ->
              let* gamma = check gamma h t in
              aux gamma rest
          | [] -> Ok gamma
        in
        aux gamma ts
    | Literal (Object _), _ ->
        raise
          (Failure "todo: checking routine for object is not yet implemented")
    | Lambda (n, e), Apply (Apply (t_function', ar), re)
      when Type.equal t_function t_function' ->
        let n' = fresh_name () in
        Env.Names.Mutable.bracketed (fun () ->
            Env.Names.Mutable.set n' ar;
            check gamma (Expr.substitute n (Variable n') e) re)
    | _, Forall (a, k, t) ->
        let a' = fresh_name () in
        let t = Type.substitute a (Skolem (a', k)) t in
        Context.scoped gamma (Quantified a') (fun gamma -> check gamma e t)
    | _ ->
        let* theta, t' = infer gamma e in
        subsumes theta (Context.apply theta t') (Context.apply theta t)

  and infer (gamma : Context.t) (e : _ Expr.t) :
      (Context.t * Type.t, Grimheart_errors.t) result =
    with_hint (InferringType e)
    @@
    match e with
    | Literal (Char _) -> Ok (gamma, t_char)
    | Literal (String _) -> Ok (gamma, t_string)
    | Literal (Int _) -> Ok (gamma, t_int)
    | Literal (Float _) -> Ok (gamma, t_float)
    | Literal (Array ts) ->
        let a = fresh_name () in
        let rec aux (gamma : Context.t) (current_t : Type.t option) :
            _ -> (Context.t * Type.t, Grimheart_errors.t) result = function
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
        aux gamma None ts
    | Literal (Object _) ->
        raise
          (Failure "todo: inference routine for object is not yet implemented")
    | Variable v -> (
        match Env.Names.find v with
        | Some t -> Ok (gamma, t)
        | None -> Error (with_message (UnknownVariable v)))
    | Lambda (v, e) ->
        let a' = fresh_name () in
        let b' = fresh_name () in
        let* delta =
          let v' = fresh_name () in
          Env.Names.Mutable.bracketed (fun () ->
              Env.Names.Mutable.set v' (Unsolved a');
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
        Env.Names.Mutable.bracketed (fun () ->
            Env.Names.Mutable.set v' t;
            infer gamma (Expr.substitute v (Variable v') e2))

  and infer_apply (gamma : Context.t) (t : Type.t) (e : _ Expr.t) :
      (Context.t * Type.t, Grimheart_errors.t) result =
    match t with
    | Forall (a, _, t) ->
        let a' = fresh_name () in
        let t = Type.substitute a (Unsolved a') t in
        infer_apply (Unsolved a' :: gamma) t e
    | Unsolved a ->
        let a' = fresh_name () in
        let b' = fresh_name () in
        let* gammaL, gammaR = Context.break_apart_at_unsolved a gamma in
        let gamma =
          insert_in_between (gammaL, gammaR) (a, a', b') Type.Sugar.fn
        in
        let* delta = check gamma e (Unsolved a') in
        Ok (delta, Type.Unsolved b')
    | Apply (Apply (t_function', i), o) when Type.equal t_function t_function'
      ->
        let* delta = check gamma e i in
        Ok (delta, o)
    | _ -> Error (with_message (CouldNotApplyTypeOn (t, e)))

  let infer_type_with (context : Context.t) (e : _ Expr.t) :
      (Type.t, Grimheart_errors.t) result =
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

  let infer_type : _ Expr.t -> (Type.t, Grimheart_errors.t) result =
    infer_type_with []
end
