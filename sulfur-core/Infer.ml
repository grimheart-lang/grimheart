open Core_kernel
open Context
open Sulfur_ast
open Expr
open Type

module Error = struct
  type t =
    | FailedSubtyping of Type.t * Type.t
    | FailedChecking of unit Expr.t * Type.t
    | FailedInfererence of unit Expr.t * Type.t
    | FailedInstantiation of string * Type.t
    | FailedKindChecking of Type.t * Type.t
    | IllFormedType of Type.t
    | UnknownVariable of string
    | ContextError of Context.Error.t
  [@@deriving eq, show]
end

let ( let* ) : (_, Error.t) result -> _ = Result.( >>= )

let ( and* ) : (_, Error.t) result -> _ = Result.Let_syntax.Let_syntax.both

(** [fresh_name ()] generates a unique name to avoid collisions. *)
let fresh_name : unit -> string =
  let i = ref (-1) in
  fun () ->
    incr i;
    "t" ^ string_of_int !i

let rec well_formed_type (context : Context.t) (_T : Type.t) :
    (unit, Error.t) result =
  match _T with
  | Constructor _ -> Ok ()
  | Variable v ->
      if Context.mem context (Quantified (v, None))
      then Ok ()
      else Error (IllFormedType _T)
  | Annotate (Variable v, k) ->
      if Context.mem context (Quantified (v, Some k))
      then Ok ()
      else Error (IllFormedType _T)
  | Unsolved u -> (
      let predicate : Element.t -> bool = function
        | (Unsolved u' | Solved (u', _)) when String.equal u u' -> true
        | _ -> false
      in
      match List.find context ~f:predicate with
      | Some _ -> Ok ()
      | None -> Error (IllFormedType _T))
  | Forall (a, _K, _A) -> (
      let* () = well_formed_type (Quantified (a, _K) :: context) _A in
      match _K with Some _K -> well_formed_type context _K | None -> Ok ())
  | Apply (_A, _B) | KindApply (_A, _B) | Annotate (_A, _B) ->
      let* _ = well_formed_type context _A
      and* _ = well_formed_type context _B in
      Ok ()

let scoped (context : Context.t) (element : Element.t)
    (action : Context.t -> (Context.t, Error.t) result) :
    (Context.t, Error.t) result =
  let* context' = action (element :: context) in
  Ok (Context.discard_up_to element context')

let scoped' (context : Context.t) (element : Element.t)
    (action : Context.t -> (Context.t * 'a, Error.t) result) :
    (Context.t * 'a, Error.t) result =
  let* context', result = action (element :: context) in
  Ok (Context.discard_up_to element context', result)

let scoped_unsolved (context : Context.t) (unsolved : string)
    (action : Context.t -> ('a, Error.t) result) : ('a, Error.t) result =
  scoped context (Marker unsolved) (fun context ->
      action (Unsolved unsolved :: context))

let scoped_unsolved' (context : Context.t) (unsolved : string)
    (action : Context.t -> (Context.t * 'a, Error.t) result) :
    (Context.t * 'a, Error.t) result =
  scoped' context (Marker unsolved) (fun context ->
      action (Unsolved unsolved :: context))

let annotate_type (_T : Type.t) (_K : Type.t option) =
  match _K with Some _K -> Annotate (_T, _K) | None -> _T

let rec subtype (gamma : Context.t) (_A : Type.t) (_B : Type.t) :
    (Context.t, Error.t) result =
  let open Primitives in
  match (_A, _B) with
  | Constructor a, Constructor b when String.equal a b ->
      (* todo: perform environment checks here? *)
      Ok gamma
  | Variable a, Variable b when String.equal a b ->
      (* `a` must exist within the context *)
      let* _ = well_formed_type gamma _A in
      Ok gamma
  (* we only need these variables to be unsolved *)
  | Unsolved a, Unsolved b
    when String.equal a b && Context.mem gamma (Unsolved a) ->
      Ok gamma
  (* function application is funky *)
  | Apply (Apply (t_function1, a1), b1), Apply (Apply (t_function2, a2), b2)
    when Type.equal t_function t_function1 && Type.equal t_function t_function2
    ->
      let* theta = subtype gamma a2 a1 in
      subtype theta (Context.apply theta b1) (Context.apply theta b2)
  | _, Forall (b, _K, _B) ->
      let b' = fresh_name () in
      let _B = Type.substitute b (annotate_type (Variable b') _K) _B in
      scoped gamma (Quantified (b', _K)) (fun gamma -> subtype gamma _A _B)
  | Forall (a, _K, _A), _ ->
      let a' = fresh_name () in
      let _A = Type.substitute a (annotate_type (Unsolved a') _K) _A in
      scoped_unsolved gamma a' (fun gamma -> subtype gamma _A _B)
  | Unsolved a, _
    when Context.mem gamma (Unsolved a)
         && not (Set.mem (Type.free_type_variables _B) a) ->
      instantiateLeft gamma a _B
  | _, Unsolved b
    when Context.mem gamma (Unsolved b)
         && not (Set.mem (Type.free_type_variables _A) b) ->
      instantiateRight gamma _A b
  | Apply (a1, b1), Apply (a2, b2) ->
      let* gamma = subtype gamma a1 a2 in
      subtype gamma b1 b2
  | _U, Annotate (_T, _K) ->
      let* gamma = check_kind gamma _U _K in
      subtype gamma _U _T
  | Annotate (_T, _K), _U ->
      let* gamma = check_kind gamma _U _K in
      subtype gamma _T _U
  | _ -> Error (FailedSubtyping (_A, _B))

and instantiateLeft (gamma : Context.t) (a : string) (_B : Type.t) :
    (Context.t, Error.t) result =
  let open Primitives in
  let* gammaL, gammaR =
    match break_apart_at (Unsolved a) gamma with
    | Ok (gammaL, gammaR) -> Ok (gammaL, gammaR)
    | Error e -> Error (ContextError e)
  in
  let solveLeft (t : Type.t) : (Context.t, Error.t) result =
    let* _ = well_formed_type gammaR _B in
    Ok (List.append gammaL (Solved (a, t) :: gammaR))
  in
  match _B with
  | Constructor _ -> solveLeft _B
  | Variable _ -> solveLeft _B
  | Unsolved b -> (
      match break_apart_at (Unsolved b) gammaL with
      | Error _ -> solveLeft _B
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
        let gammaM =
          [
            Element.Solved (a, Sugar.fn (Type.Unsolved a') (Type.Unsolved b'))
          ; Element.Unsolved a'
          ; Element.Unsolved b'
          ]
        in
        List.concat [gammaL; gammaM; gammaR]
      in
      let* theta = instantiateRight gamma _A a' in
      instantiateLeft theta b' (Context.apply theta _B)
  | Forall (b, _K, _B) ->
      scoped gamma
        (Quantified (b, _K))
        (fun gamma -> instantiateLeft gamma b _B)
  | Apply (_A, _B) ->
      let a' = fresh_name () in
      let b' = fresh_name () in
      let gamma =
        let gammaM =
          [
            Element.Solved (a, Sugar.ap (Type.Unsolved a') (Type.Unsolved b'))
          ; Element.Unsolved a'
          ; Element.Unsolved b'
          ]
        in
        List.concat [gammaL; gammaM; gammaR]
      in
      let* theta = instantiateLeft gamma a' _A in
      instantiateLeft theta b' (Context.apply theta _B)
  | KindApply (_, _) ->
      (* KindApply isn't user-facing, so we shouldn't ever handle it when
         performing instantiation. *)
      raise (Failure "instantiateLeft: called with KindApply")
  | Annotate (_A, _B) ->
      let a' = fresh_name () in
      let b' = fresh_name () in
      let gamma =
        let gammaM =
          [
            Element.Solved
              (a, Type.Annotate (Type.Unsolved a', Type.Unsolved b'))
          ; Element.Unsolved a'
          ; Element.Unsolved b'
          ]
        in
        List.concat [gammaL; gammaM; gammaR]
      in
      let* theta = instantiateLeft gamma a' _A in
      instantiateLeft theta b' (Context.apply theta _B)

and instantiateRight (gamma : Context.t) (_A : Type.t) (b : string) :
    (Context.t, Error.t) result =
  let open Primitives in
  let* gammaL, gammaR =
    match break_apart_at (Unsolved b) gamma with
    | Ok (gammaL, gammaR) -> Ok (gammaL, gammaR)
    | Error e -> Error (ContextError e)
  in
  let solveRight (t : Type.t) : (Context.t, Error.t) result =
    let* _ = well_formed_type gammaR _A in
    Ok (List.append gammaL (Solved (b, t) :: gammaR))
  in
  match _A with
  | Constructor _ -> solveRight _A
  | Variable _ -> solveRight _A
  | Unsolved b -> (
      match break_apart_at (Unsolved b) gammaL with
      | Error _ -> solveRight _A
      | Ok (gammaLL, gammaLR) ->
          let gammaL =
            List.append gammaLL (Solved (b, Unsolved b) :: gammaLR)
          in
          let gamma = List.append gammaL (Unsolved b :: gammaR) in
          Ok gamma)
  | Apply (Apply (t_function', _A), _B) when Type.equal t_function t_function'
    ->
      let a' = fresh_name () in
      let b' = fresh_name () in
      let gamma =
        let gammaM =
          [
            Element.Solved (b, Sugar.fn (Type.Unsolved a') (Type.Unsolved b'))
          ; Element.Unsolved a'
          ; Element.Unsolved b'
          ]
        in
        List.concat [gammaL; gammaM; gammaR]
      in
      let* theta = instantiateLeft gamma a' _A in
      instantiateRight theta (Context.apply theta _B) b'
  | Forall (b, _K, _B) ->
      let b' = fresh_name () in
      let _B = Type.substitute b (annotate_type (Unsolved b') _K) _B in
      scoped_unsolved gamma b' (fun gamma -> instantiateRight gamma _B b')
  | Apply (_A, _B) ->
      let a' = fresh_name () in
      let b' = fresh_name () in
      let gamma =
        let gammaM =
          [
            Element.Solved (b, Sugar.ap (Type.Unsolved a') (Type.Unsolved b'))
          ; Element.Unsolved a'
          ; Element.Unsolved b'
          ]
        in
        List.concat [gammaL; gammaM; gammaR]
      in
      let* theta = instantiateRight gamma _A a' in
      instantiateRight theta (Context.apply theta _B) b'
  | KindApply (_, _) ->
      (* KindApply isn't user-facing, so we shouldn't ever handle it when
         performing instantiation. *)
      raise (Failure "instantiateRight: called with KindApply")
  | Annotate (_A, _B) ->
      let a' = fresh_name () in
      let b' = fresh_name () in
      let gamma =
        let gammaM =
          [
            Element.Solved
              (b, Type.Annotate (Type.Unsolved a', Type.Unsolved b'))
          ; Element.Unsolved a'
          ; Element.Unsolved b'
          ]
        in
        List.concat [gammaL; gammaM; gammaR]
      in
      let* theta = instantiateRight gamma _A a' in
      instantiateRight theta (Context.apply theta _B) b'

and check (gamma : Context.t) (e : _ Expr.t) (_A : Type.t) :
    (Context.t, Error.t) result =
  let open Primitives in
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
      raise (Failure "todo: checking routine for object is not yet implemented")
  | Lambda (n, e), Apply (Apply (t_function', _A1), _A2)
    when Type.equal t_function t_function' ->
      let n' = fresh_name () in
      scoped gamma
        (Variable (n', _A1))
        (fun gamma -> check gamma (Expr.substitute n (Variable n') e) _A2)
  | _, Forall (a, _K, _A) ->
      let a' = fresh_name () in
      let _A = Type.substitute a (annotate_type (Variable a') _K) _A in
      scoped gamma (Quantified (a', _K)) (fun gamma -> check gamma e _A)
  | _ ->
      let* theta, _A' = infer gamma e in
      subtype theta (Context.apply theta _A') (Context.apply theta _A)

and infer (gamma : Context.t) (e : _ Expr.t) :
    (Context.t * Type.t, Error.t) result =
  let open Primitives in
  match e with
  | Literal (Char _) -> Ok (gamma, t_char)
  | Literal (String _) -> Ok (gamma, t_string)
  | Literal (Int _) -> Ok (gamma, t_int)
  | Literal (Float _) -> Ok (gamma, t_float)
  | Literal (Array _As) ->
      let a = fresh_name () in
      let rec aux (gamma : Context.t) (current_t : Type.t option) = function
        | h :: t -> (
            let* gamma, inferred_t = infer gamma h in
            match (inferred_t, current_t) with
            | _, Some current_t ->
                (* todo: make this rethrow a better error *)
                let* gamma = subtype gamma inferred_t current_t in
                aux gamma (Some inferred_t) t
            | _, None -> aux gamma (Some inferred_t) t)
        | [] -> (
            (* NOTE: These annotations propagate up but they aren't erased at
               any point by the top-level generalization algorithm. As such,
               tests would have to explicitly look for annotations... for
               now. *)
            match current_t with
            | Some current_t ->
                Ok (gamma, Apply (t_array, Annotate (current_t, t_type)))
            | None ->
                Ok
                  ( Unsolved a :: gamma
                  , Apply (t_array, Annotate (Unsolved a, t_type)) ))
      in
      aux gamma None _As
  | Literal (Object _) ->
      raise
        (Failure "todo: inference routine for object is not yet implemented")
  | Variable v -> (
      let find_variable = function
        | Element.Variable (v', t) when String.equal v v' -> Some t
        | _ -> None
      in
      match List.find_map gamma ~f:find_variable with
      | Some t -> Ok (gamma, t)
      | None -> Error (UnknownVariable v))
  | Lambda (v, e) ->
      let a' = fresh_name () in
      let b' = fresh_name () in
      let* delta =
        let v' = fresh_name () in
        scoped
          (Unsolved b' :: Unsolved a' :: gamma)
          (Variable (v', Unsolved a'))
          (fun gamma ->
            check gamma (Expr.substitute v (Variable v') e) (Unsolved b'))
      in
      Ok (delta, Sugar.fn (Unsolved a') (Unsolved b'))
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
      infer (Variable (v', t) :: gamma) (Expr.substitute v (Variable v') e2)

and infer_apply (gamma : Context.t) (_A : Type.t) (e : _ Expr.t) :
    (Context.t * Type.t, Error.t) result =
  let open Primitives in
  match _A with
  | Forall (a, _K, _A) ->
      let a' = fresh_name () in
      let _A = Type.substitute a (annotate_type (Unsolved a') _K) _A in
      infer_apply (Unsolved a' :: gamma) _A e
  | Unsolved a ->
      let a' = fresh_name () in
      let b' = fresh_name () in
      let* gammaL, gammaR =
        match break_apart_at (Unsolved a') gamma with
        | Ok (gammaL, gammaR) -> Ok (gammaL, gammaR)
        | Error e -> Error (ContextError e)
      in
      let gammaM =
        [
          Element.Solved (a, Sugar.fn (Type.Unsolved a') (Type.Unsolved b'))
        ; Element.Unsolved a'
        ; Element.Unsolved b'
        ]
      in
      let gamma = List.concat [gammaL; gammaM; gammaR] in
      let* delta = check gamma e (Unsolved a') in
      Ok (delta, Unsolved b')
  | Apply (Apply (t_function', _A), _B) when Type.equal t_function t_function'
    ->
      let* delta = check gamma e _A in
      Ok (delta, _B)
  | _ -> Error (FailedInfererence (e, _A))

and check_kind (gamma : Context.t) (_T : Type.t) (_K : Type.t) :
    (Context.t, Error.t) result =
  let open Primitives in
  match (_T, _K) with
  | Constructor _, Constructor "Type" when is_primitive_type _T -> Ok gamma
  | ( Constructor _
    , Apply (Apply (t_function', Constructor "Type"), Constructor "Type") )
    when Type.equal t_function t_function' && is_primitive_type_type _T ->
      Ok gamma
  | ( Constructor "Function"
    , Apply
        ( Apply (Constructor "Function", Constructor "Type")
        , Apply
            ( Apply (Constructor "Function", Constructor "Type")
            , Constructor "Type" ) ) ) ->
      Ok gamma
  | Constructor _, _ ->
      raise
        (Failure "todo: arbitrary constructors should look up the environment")
  | _, Forall (a, _K', _A) ->
      let a' = fresh_name () in
      let _A = Type.substitute a (annotate_type (Variable a') _K') _A in
      scoped gamma
        (Quantified (a', _K'))
        (function gamma -> check_kind gamma _T _A)
  | _ ->
      let* theta, _TK = infer_kind gamma _T in
      subtype theta (Context.apply theta _TK) (Context.apply theta _K)

and infer_kind (gamma : Context.t) (_T : Type.t) :
    (Context.t * Type.t, Error.t) result =
  let open Primitives in
  match _T with
  | Constructor _ when is_primitive_type _T -> Ok (gamma, t_type)
  | Constructor _ when is_primitive_type_type _T ->
      Ok (gamma, Sugar.fn t_type t_type)
  | Constructor "Function" ->
      Ok (gamma, Sugar.fn t_type (Sugar.fn t_type t_type))
  | Constructor _ ->
      raise (Failure "Kind synthesis failed for arbitrary constructors.")
  | Apply (Apply (t_function', _A), _B) when Type.equal t_function t_function'
    ->
      let* gamma = check_kind gamma _A t_type in
      let* gamma = check_kind gamma _B t_type in
      Ok (gamma, t_type)
  | Forall (a, _K, _A) ->
      let a' = fresh_name () in
      let _A = Type.substitute a (annotate_type (Unsolved a') _K) _A in
      scoped_unsolved' gamma a' (fun gamma -> infer_kind gamma _A)
  | Unsolved u ->
      let u' = fresh_name () in
      Ok (Unsolved u' :: gamma, Type.substitute u (Unsolved u') _T)
  | Variable v -> (
      let find_variable : Element.t -> Type.t option = function
        | Variable (v', t) when String.equal v v' -> Some t
        | _ -> None
      in
      match List.find_map gamma ~f:find_variable with
      | Some t -> Ok (gamma, t)
      | None -> Error (UnknownVariable v))
  | Apply (_A, _B) ->
      let* gamma, _K = infer_kind gamma _A in
      infer_apply_kind gamma _K _B
  | Annotate (_A, _B) ->
      let* gamma = check_kind gamma _A _B in
      Ok (gamma, _B)
  | KindApply (_A, _B) -> (
      let* gamma, _A_K = infer_kind gamma _A in
      match _A_K with
      | Forall (a, Some k, t) ->
          let* gamma = check_kind gamma _B k in
          Ok (gamma, Type.substitute a _B t)
      | _ -> failwith "infer_kind: forall binder has no kind")

and infer_apply_kind (gamma : Context.t) (_K : Type.t) (_X : Type.t) =
  let open Primitives in
  match _K with
  | Forall (a, _K', _K) ->
      let a' = fresh_name () in
      let _K = Type.substitute a (annotate_type (Unsolved a') _K') _K in
      infer_apply_kind (Unsolved a' :: gamma) _K _X
  | Unsolved a ->
      let a' = fresh_name () in
      let b' = fresh_name () in
      let* gammaL, gammaR =
        match break_apart_at (Unsolved a) gamma with
        | Ok (gammaL, gammaR) -> Ok (gammaL, gammaR)
        | Error e -> Error (ContextError e)
      in
      let gammaM =
        [
          Element.Solved (a, Sugar.fn (Type.Unsolved a') (Type.Unsolved b'))
        ; Element.Unsolved a'
        ; Element.Unsolved b'
        ]
      in
      let gamma = List.concat [gammaL; gammaM; gammaR] in
      let* delta = check_kind gamma _X (Unsolved a') in
      Ok (delta, Unsolved b')
  | Apply (Apply (t_function', _A), _B) when Type.equal t_function t_function'
    ->
      let* delta = check_kind gamma _X _A in
      Ok (delta, _B)
  | _ -> raise (Failure "Impossible case in synth_app_kind")

let infer_type_with (context : Context.t) (e : _ Expr.t) :
    (Type.t, Error.t) result =
  let* delta, poly_type = infer context e in
  let fresh_variable =
    let i = ref (-1) in
    fun () ->
      incr i;
      String.of_char (Char.of_int_exn (97 + (!i mod 26)))
  in
  let algebra element poly_type =
    match element with
    | Element.Unsolved u ->
        let u' = fresh_variable () in
        Forall (u', None, Type.substitute u (Variable u') poly_type)
    | _ -> poly_type
  in
  Ok (List.fold_right delta ~f:algebra ~init:(Context.apply delta poly_type))

let infer_type : _ Expr.t -> (Type.t, Error.t) result = infer_type_with []
