open Core_kernel

open Context
open Expr
open Type

type e =
  | FailedSubtyping of Type.t * Type.t
  | FailedChecking of unit Expr.t * Type.t
  | FailedInfererence of unit Expr.t * Type.t
  | FailedInstantiation of string * Type.t
  | FailedKindChecking of Type.t * Type.t
  | IllFormedType of Type.t
  | UnknownVariable of string
  | ContextError of Context.e

let (let*) = Result.(>>=)
let (and*) = Result.Let_syntax.Let_syntax.both

let fresh_name : unit -> string =
  let i = ref (-1) in
  function () ->
    incr i;
    "t" ^ string_of_int !i

let rec well_formed_type (context : Context.t) (t : Type.t) : (unit, e) Result.t =
  match t with
  | Constructor _ ->
     Ok ()
  | Variable v ->
     if Context.mem context (Quantified v) then
       Ok ()
     else
       Error (IllFormedType t)
  | Unsolved u ->
     let predicate : Element.t -> bool = function
       | Unsolved u' | Solved (u', _) when String.equal u u' ->
          true
       | _ ->
          false
     in
     ( match List.find context ~f:predicate with
       | Some _ -> Ok ()
       | None -> Error (IllFormedType t)
     )
  | Forall (a, _, t) ->
     well_formed_type (Quantified a :: context) t
  | Apply (t1, t2) | KindApply (t1, t2) | Annotate (t1, t2) ->
     let* _ = well_formed_type context t1
     and* _ = well_formed_type context t2
     in Ok ()

let scoped context element action =
  let* context' = action (element :: context) in
  Ok (Context.discard_up_to element context')

let scoped_unsolved context unsolved action =
  scoped context (Element.Marker unsolved)
    (function context -> action (Element.Unsolved unsolved :: context))

let rec subtype (gamma : Context.t) (_A : Type.t) (_B : Type.t) : (Context.t, e) result =
  let open Primitives in
  match (_A, _B) with
  | Constructor a, Constructor b when String.equal a b ->
     (* todo: perform environment checks here? *)
     Ok gamma
  | Variable a, Variable b when String.equal a b ->
     (* `a` must exist within the context *)
     let* _ = well_formed_type gamma _A in Ok gamma
  (* we only need these variables to be unsolved *)
  | Unsolved a, Unsolved b
       when String.equal a b && Context.mem gamma (Unsolved a) ->
     Ok gamma
  (* function application is funky *)
  | Apply (Apply (t_function1, a1), b1)
  , Apply (Apply (t_function2, a2), b2)
       when Type.equal t_function t_function1
         && Type.equal t_function t_function2 ->
     let* theta = subtype gamma a2 a1 in
     subtype theta (Context.apply theta b1) (Context.apply theta b2)
  | _, Forall (b, _, _B) ->
     let b' = fresh_name () in
     scoped gamma (Quantified b')
       (function gamma -> subtype gamma _A (Type.substitute b (Variable b') _B))
  | Forall (a, _, _A), _ ->
     let a' = fresh_name () in
     scoped_unsolved gamma a'
       (function gamma -> subtype gamma (Type.substitute a (Unsolved a') _A) _B)
  | Unsolved a, _
       when Context.mem gamma (Unsolved a)
         && not (Set.mem (Type.free_type_variables _B) a) ->
     instantiateLeft gamma a _B
  | _, Unsolved b
       when Context.mem gamma (Unsolved b)
            && not (Set.mem (Type.free_type_variables _A) b) ->
     instantiateRight gamma _A b
  | Apply (a1, b1), Apply (a2, b2) ->
     let* gamma = subtype gamma a1 a2 in subtype gamma b1 b2
  | _A, Annotate (_B, _) | Annotate (_A, _), _B ->
     subtype gamma _A _B
  | _ ->
     Error (FailedSubtyping (_A, _B))

and instantiateLeft (gamma : Context.t) (a : string) (_A : Type.t) : (Context.t, e) result =
  let open Primitives in
  let* (gammaL, gammaR) =
    match break_apart_at (Unsolved a) gamma with
    | Ok (gammaL, gammaR) -> Ok (gammaL, gammaR)
    | Error e -> Error (ContextError e)
  in
  let solveLeft (t : Type.t) : (Context.t, e) result =
    let* _ = well_formed_type gammaR _A in
    Ok (List.append gammaL (Solved (a, t) :: gammaR))
  in
  match _A with
  | Constructor _ ->
     solveLeft _A
  | Variable _ ->
     solveLeft _A
  | Unsolved b ->
     ( match break_apart_at (Unsolved b) gammaL with
       | Error _ ->
          solveLeft _A
       | Ok (gammaLL, gammaLR) ->
          let gammaL =
            List.append gammaLL (Solved (b, Unsolved a) :: gammaLR)
          in
          let gamma =
            List.append gammaL (Unsolved a :: gammaR)
          in
          Ok gamma
     )
  | Apply (Apply (t_function', _A), _B)
       when Type.equal t_function t_function' ->
     let a' = fresh_name () in
     let b' = fresh_name () in
     let gamma =
       let gammaM =
         [ Element.Solved (a, Sugar.fn (Type.Unsolved a') (Type.Unsolved b'))
         ; Element.Unsolved a'
         ; Element.Unsolved b'
         ]
       in
       List.concat [gammaL;gammaM;gammaR]
     in
     let* theta =
       instantiateRight gamma _A a'
     in
     instantiateLeft theta b' (Context.apply theta _B)
  | Forall (b, _, _B) ->
     scoped gamma (Quantified b)
       (function gamma -> instantiateLeft gamma b _B)
  | Apply (_A, _B) ->
     let a' = fresh_name () in
     let b' = fresh_name () in
     let gamma =
       let gammaM =
         [ Element.Solved (a, Sugar.ap (Type.Unsolved a') (Type.Unsolved b'))
         ; Element.Unsolved a'
         ; Element.Unsolved b'
         ]
       in
       List.concat [gammaL;gammaM;gammaR]
     in
     let* theta =
       instantiateLeft gamma a' _A
     in
     instantiateLeft theta b' (Context.apply theta _B)
  | KindApply (_A, _B) ->
     let a' = fresh_name () in
     let b' = fresh_name () in
     let gamma =
       let gammaM =
         [ Element.Solved (a, Type.KindApply (Type.Unsolved a', Type.Unsolved b'))
         ; Element.Unsolved a'
         ; Element.Unsolved b'
         ]
       in
       List.concat [gammaL;gammaM;gammaR]
     in
     let* theta =
       instantiateLeft gamma a' _A
     in
     instantiateLeft theta b' (Context.apply theta _B)
  | Annotate (_A, _B) ->
     let a' = fresh_name () in
     let b' = fresh_name () in
     let gamma =
       let gammaM =
         [ Element.Solved (a, Type.Annotate (Type.Unsolved a', Type.Unsolved b'))
         ; Element.Unsolved a'
         ; Element.Unsolved b'
         ]
       in
       List.concat [gammaL;gammaM;gammaR]
     in
     let* theta =
       instantiateLeft gamma a' _A
     in
     instantiateLeft theta b' (Context.apply theta _B)

and instantiateRight (gamma : Context.t) (_A : Type.t) (a : string) : (Context.t, e) result =
  let open Primitives in
  let* (gammaL, gammaR) =
    match break_apart_at (Unsolved a) gamma with
    | Ok (gammaL, gammaR) -> Ok (gammaL, gammaR)
    | Error e -> Error (ContextError e)
  in
  let solveLeft (t : Type.t) : (Context.t, e) result =
    let* _ = well_formed_type gammaR _A in
    Ok (List.append gammaL (Solved (a, t) :: gammaR))
  in
  match _A with
  | Constructor _ ->
     solveLeft _A
  | Variable _ ->
     solveLeft _A
  | Unsolved b ->
     ( match break_apart_at (Unsolved b) gammaL with
       | Error _ ->
          solveLeft _A
       | Ok (gammaLL, gammaLR) ->
          let gammaL =
            List.append gammaLL (Solved (b, Unsolved a) :: gammaLR)
          in
          let gamma =
            List.append gammaL (Unsolved a :: gammaR)
          in
          Ok gamma
     )
  | Apply (Apply (t_function', _A), _B)
       when Type.equal t_function t_function' ->
     let a' = fresh_name () in
     let b' = fresh_name () in
     let gamma =
       let gammaM =
         [ Element.Solved (a, Sugar.fn (Type.Unsolved a') (Type.Unsolved b'))
         ; Element.Unsolved a'
         ; Element.Unsolved b'
         ]
       in
       List.concat [gammaL;gammaM;gammaR]
     in
     let* theta =
       instantiateLeft gamma a' _A
     in
     instantiateRight theta (Context.apply theta _B) b'
  | Forall (b, _, _B) ->
     let b' = fresh_name () in
     scoped_unsolved gamma b'
       (function gamma -> instantiateLeft gamma b' (Type.substitute b (Unsolved b') _B))
  | Apply (_A, _B) ->
     let a' = fresh_name () in
     let b' = fresh_name () in
     let gamma =
       let gammaM =
         [ Element.Solved (a, Sugar.ap (Type.Unsolved a') (Type.Unsolved b'))
         ; Element.Unsolved a'
         ; Element.Unsolved b'
         ]
       in
       List.concat [gammaL;gammaM;gammaR]
     in
     let* theta =
       instantiateRight gamma _A a'
     in
     instantiateRight theta (Context.apply theta _B) b'
  | KindApply (_A, _B) ->
     let a' = fresh_name () in
     let b' = fresh_name () in
     let gamma =
       let gammaM =
         [ Element.Solved (a, Type.KindApply (Type.Unsolved a', Type.Unsolved b'))
         ; Element.Unsolved a'
         ; Element.Unsolved b'
         ]
       in
       List.concat [gammaL;gammaM;gammaR]
     in
     let* theta =
       instantiateRight gamma _A a'
     in
     instantiateRight theta (Context.apply theta _B) b'
  | Annotate (_A, _B) ->
     let a' = fresh_name () in
     let b' = fresh_name () in
     let gamma =
       let gammaM =
         [ Element.Solved (a, Type.Annotate (Type.Unsolved a', Type.Unsolved b'))
         ; Element.Unsolved a'
         ; Element.Unsolved b'
         ]
       in
       List.concat [gammaL;gammaM;gammaR]
     in
     let* theta =
       instantiateRight gamma _A a'
     in
     instantiateRight theta (Context.apply theta _B) b'

and check (gamma : Context.t) (e : _ Expr.t) (_A: Type.t) : (Context.t, e) result =
  let open Primitives in
  match (e, _A) with
  | Literal l, (Constructor c) ->
     ( match (l, c) with
       | Char _, "Char"
       | String _, "String"
       | Int _, "Int"
       | Float _, "Float" ->
          Ok gamma
       | Array _, "Array" ->
          raise (Failure "todo: checking routine for arrays is not yet implemented")
       | Object _, "Object" ->
          raise (Failure "todo: checking routine for objects is not yet implemented")
       | _ ->
          Error (FailedChecking (e, _A))
     )
  | Lambda (n, e), Apply (Apply (t_function', _A1), _A2)
       when Type.equal t_function t_function' ->
     let n' = fresh_name () in
     scoped gamma (Variable (n', _A1))
       (function gamma -> check gamma (Expr.substitute n (Variable n') e)_A2)
  | _, Forall (a, _, _A) ->
     let a' = fresh_name () in
     scoped gamma (Quantified a')
       (function gamma -> check gamma e (Type.substitute a (Variable a') _A))
  | _ ->
     let* (theta, _A') = infer gamma e in
     subtype theta (Context.apply theta _A') (Context.apply theta _A)

and infer (gamma : Context.t) (e : _ Expr.t) : (Context.t * Type.t, e) result =
  let open Primitives in
  match e with
  | Literal l ->
     let t =
     ( match l with
       | Literal.Char _ -> t_char
       | Literal.String _ -> t_string
       | Literal.Int _ -> t_int
       | Literal.Float _ -> t_float
       | Literal.Array _ ->
          raise (Failure "todo: inference routine for array is not yet implemented")
       | Literal.Object (_, _) ->
          raise (Failure "todo: inference routine for object is not yet implemented")
     )
     in Ok (gamma, t)
  | Variable v ->
     let find_variable = function
       | Element.Variable (v', t) when String.equal v v' -> Some t
       | _ -> None
     in
     ( match List.find_map gamma ~f:find_variable with
       | Some t ->
          Ok (gamma, t)
       | None ->
          Error (UnknownVariable v)
     )
  | Lambda (v, e) ->
     let a' = fresh_name () in
     let b' = fresh_name () in
     let* delta =
       let v' = fresh_name () in
       scoped (Unsolved b' :: Unsolved a' :: gamma) (Variable (v', Unsolved a'))
         (function gamma -> check gamma (Expr.substitute v (Variable v') e) (Unsolved b'))
     in
     Ok (delta, Sugar.fn (Unsolved a') (Unsolved b'))
  | Apply (f, x) ->
     let* (theta, t) = infer gamma f in
     infer_apply theta (Context.apply theta t) x
  | Annotate (e, t) ->
     let* theta = check gamma e t in Ok (theta, t)
  | Let (v, t, e1, e2) ->
     let* (gamma, t) =
       match t with
       | Some t ->
          let* gamma = check gamma e1 t in Ok (gamma, t)
       | None ->
          infer gamma e1
     in
     let v' = fresh_name () in
     infer
       (Variable (v', t) :: gamma)
       (Expr.substitute v (Variable v') e2)

and infer_apply (gamma : Context.t) (_A : Type.t) (e : _ Expr.t) : (Context.t * Type.t, e) result =
  let open Primitives in
  match _A with
  | Forall (a, _, _A) ->
     let a' = fresh_name () in
     infer_apply (Unsolved a' :: gamma) (Type.substitute a (Unsolved a') _A) e
  | Unsolved a ->
     let a' = fresh_name () in
     let b' = fresh_name () in
     let* (gammaL, gammaR) =
       match break_apart_at (Unsolved a') gamma with
       | Ok (gammaL, gammaR) -> Ok (gammaL, gammaR)
       | Error e -> Error (ContextError e)
     in
     let gammaM =
       [ Element.Solved (a, Sugar.fn (Type.Unsolved a') (Type.Unsolved b'))
       ; Element.Unsolved a'
       ; Element.Unsolved b'
       ]
     in
     let gamma = List.concat [gammaL;gammaM;gammaR] in
     let* delta = check gamma e (Unsolved a') in
     Ok (delta, Unsolved b')
  | Apply (Apply (t_function', _A), _B)
       when Type.equal t_function t_function' ->
     let* delta = check gamma e _A in
     Ok (delta, _B)
  | _ ->
     Error (FailedInfererence (e, _A))

let infer_type_with (context : Context.t) (e : _ Expr.t) : (Type.t, e) result =
  let* (delta, poly_type) = infer context e in
  let fresh_variable =
    let i = ref (-1) in
    function () ->
      incr i;
      String.of_char (Char.of_int_exn (97 + (!i mod 26)))
  in
  let algebra element poly_type =
    match element with
    | Element.Unsolved u ->
       let u' = fresh_variable () in
       Forall (u', None, Type.substitute u (Variable u') poly_type)
    | _ ->
       poly_type
  in
  Ok (List.fold_right delta ~f:algebra ~init:(Context.apply delta poly_type))

let infer_type : _ Expr.t -> (Type.t, e) result = infer_type_with []

let rec check_kind (gamma : Context.t) (_T : Type.t) (_K : Type.t) : (Context.t, e) result =
  let open Primitives in
  match (_T, _K) with
  | Constructor _, Constructor "Type"
       when is_primitive_type _T ->
     Ok gamma
  | Constructor _, Apply (Apply (t_function', Constructor "Type"), Constructor "Type")
       when Type.equal t_function t_function'
         && is_primitive_type_type _T ->
     Ok gamma
  | Constructor "Function"
  , Apply
      ( Apply
          ( Constructor "Function"
          , Constructor "Type"
          )
      , Apply
          ( Apply
              ( Constructor "Function"
              , Constructor "Type"
              )
          , Constructor "Type"
          )
      ) ->
     Ok gamma
  | Constructor _, _ ->
     raise (Failure "Kind checking failed for arbitrary constructors.")
  | _, Forall (a, _, _A) ->
     let a' = fresh_name () in
     scoped gamma (Quantified a')
       (function gamma -> check_kind gamma _T (Type.substitute a (Variable a') _A))
  | _ ->
     let* (theta, _TK) = infer_kind gamma _T in
     subtype theta (Context.apply theta _TK) (Context.apply theta _K)

and infer_kind (gamma : Context.t) (_T : Type.t) : (Context.t * Type.t, e) result =
  let open Primitives in
  match _T with
  | Constructor _ when is_primitive_type _T ->
     Ok (gamma, t_type)
  | Constructor _ when is_primitive_type_type _T ->
     Ok (gamma, Sugar.fn t_type t_type)
  | Constructor "Function" ->
     Ok (gamma, Sugar.fn t_type (Sugar.fn t_type t_type))
  | Constructor _ ->
     raise (Failure "Kind synthesis failed for arbitrary constructors.")
  | Apply (Apply (t_function', _A), _B)
       when Type.equal t_function t_function' ->
     let* gamma = check_kind gamma _A t_type in
     let* gamma = check_kind gamma _B t_type in
     Ok (gamma, t_type)
  | Forall (a, _, _A) ->
     let a' = fresh_name () in
     infer_kind (Unsolved a' :: gamma) (Type.substitute a (Unsolved a') _A)
  | Unsolved u ->
     Ok (Unsolved u :: gamma, _T)
     (* raise (Failure "Cannot synthesize unknowns in kinds.") *)
  | Variable v ->
     let find_variable : Element.t -> Type.t option = function
       | Variable (v', t) when String.equal v v' -> Some t
       | _ -> None
     in
     ( match List.find_map gamma ~f:find_variable with
       | Some t ->
          Ok (gamma, t)
       | None ->
          Error (UnknownVariable v)
     )
  | Apply (_A, _B) ->
     let* (gamma, _K) = infer_kind gamma _A in
     infer_apply_kind gamma _K _B
  | Annotate (_A, _B) ->
     let* gamma = check_kind gamma _A _B in Ok (gamma, _B)
  | KindApply (_A, _B) ->
     let* (gamma, _A_K) = infer_kind gamma _A in
     match _A_K with
     | Forall (a, Some k, t) ->
        let* gamma = check_kind gamma _B k in
        Ok (gamma, Type.substitute a _B t)
     | _ ->
        failwith "infer_kind: forall binder has no kind"

and infer_apply_kind (gamma : Context.t) (_K : Type.t) (_X : Type.t) =
  let open Primitives in
  match _K with
  | Forall (a, _, _K) ->
     let a' = fresh_name () in
     infer_apply_kind (Unsolved a' :: gamma) (Type.substitute a (Unsolved a') _K) _X
  | Unsolved a ->
     let a' = fresh_name () in
     let b' = fresh_name () in
     let* (gammaL, gammaR) =
       match break_apart_at (Unsolved a) gamma with
       | Ok (gammaL, gammaR) -> Ok (gammaL, gammaR)
       | Error e -> Error (ContextError e)
     in
     let gammaM =
       [ Element.Solved (a, Sugar.fn (Type.Unsolved a') (Type.Unsolved b'))
       ; Element.Unsolved a'
       ; Element.Unsolved b'
       ]
     in
     let gamma = List.concat [gammaL;gammaM;gammaR] in
     let* delta = check_kind gamma _X (Unsolved a') in
     Ok (delta, Unsolved b')
  | Apply (Apply (t_function', _A), _B)
       when Type.equal t_function t_function' ->
     let* delta = check_kind gamma _X _A in Ok (delta, _B)
  | _ ->
     raise (Failure "Impossible case in synth_app_kind")
