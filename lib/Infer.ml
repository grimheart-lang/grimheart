open Core_kernel
open Context
open Syntax

type error =
  [ `CannotSubtype of poly_t * poly_t
  | `CannotFindVariable of string * Context.t
  | `CannotSynthesizeApplication of poly_t
  | `NotWellFormed of Context.t * poly_t
  | Context.error
  ]

let (let*) r f = Result.Let_syntax.Let_syntax.bind r ~f:f
let (and*) l r = Result.Let_syntax.Let_syntax.both l r

let fresh_name : unit -> string =
  let i = ref 0 in
  function () ->
    let suffix = string_of_int !i in
    incr i;
    "t" ^ suffix

let rec well_formed_type (context : Context.t) (poly_type : poly_t) : (unit, [> error]) result =
  match poly_type with
  | PLiteral -> Ok ()
  | PVariable v ->
     if List.mem context (CQuantified v) ~equal:equal_element_t then
       Ok ()
     else
       Error (`NotWellFormed (context, poly_type))
  | PUnsolved u ->
     let predicate = function
       | CUnsolved u' | CSolved (u', _) when String.(u = u') ->
          true
       | _ ->
          false
     in
     if Option.is_some (List.find context ~f:predicate) then
       Ok ()
     else
       Error (`NotWellFormed (context, poly_type))
  | PFunction (a, b) ->
     let* _ = well_formed_type context a
     and* _ = well_formed_type context b
     in Ok ()
  | PForall (a, t) ->
     well_formed_type (CQuantified a :: context) t

let scoped (context : Context.t) (element : element_t) (action : Context.t -> (Context.t, [> error]) result) =
  let* context' = action (element :: context) in
  Ok (discard_up_to element context')

let scoped_unsolved context unsolved action =
  scoped context (CMarker unsolved)
    (function context -> action (CUnsolved unsolved :: context))

let rec subtype (gamma : Context.t) (_A : poly_t) (_B : poly_t) : (Context.t, [> error]) result =
  match (_A, _B) with
  | PLiteral, PLiteral ->
     Ok gamma
  | PVariable _a, PVariable _b when String.(_a = _b) ->
     let* _ = well_formed_type gamma _A in Ok gamma
  | PUnsolved _a, PUnsolved _b when String.(_a = _b) && Context.mem gamma (CUnsolved _a) ->
     Ok gamma
  | PFunction (_a, _b), PFunction (_a', _b') ->
     let* theta = subtype gamma _a' _a in
     subtype theta (Context.apply theta _b) (Context.apply theta _b')
  | _, PForall (_b, _B) ->
     let _b' = fresh_name () in
     scoped gamma (CQuantified _b')
       (function gamma -> subtype gamma _A (poly_subst _b (PVariable _b') _B))
  | PForall (_a, _A), _ ->
     let _a' = fresh_name () in
     scoped_unsolved gamma _a'
       (function gamma -> subtype gamma (poly_subst _a (PUnsolved _a') _A) _B)
  | PUnsolved _a, _
       when Context.mem gamma (CUnsolved _a)
         && not (Set.mem (free_type_variables _B) _a) ->
     instantiateLeft gamma _a _B
  | _, PUnsolved _b
       when Context.mem gamma (CUnsolved _b)
         && not (Set.mem (free_type_variables _A) _b) ->
     instantiateRight gamma _A _b
  | _ ->
     Error (`CannotSubtype (_A, _B))

and instantiateLeft (gamma : Context.t) (_a : string) (_A : poly_t) : (Context.t, [> error]) result =
  let* (gammaL, gammaR) = break_apart_at (CUnsolved _a) gamma in
  let solveLeft (_t : mono_t) : (Context.t, [> error]) result =
    let* _ = well_formed_type gammaR _A in
    Ok (List.append gammaL (CSolved (_a, _t) :: gammaR))
  in
  match _A with
  | PLiteral -> solveLeft MLiteral
  | PVariable v -> solveLeft (MVariable v)
  | PUnsolved _b ->
     ( match break_apart_at (CUnsolved _b) gammaL with
       | Error `FailedToBreakApart ->
          solveLeft (MUnsolved _b)
       | Ok (gammaLL, gammaLR) ->
          let gammaL =
            List.append gammaLL (CSolved (_b, MUnsolved _a) :: gammaLR)
          in
          let gamma =
            List.append gammaL (CUnsolved _a :: gammaR)
          in
          Ok gamma
     )
  | PFunction (_A1, _A2) ->
     let a1 = fresh_name () in
     let a2 = fresh_name () in
     let gamma =
       let gammaM =
         [CSolved (_a, MFunction (MUnsolved a1, MUnsolved a2)); CUnsolved a1; CUnsolved a2]
       in
       List.concat [gammaL;gammaM;gammaR]
     in
     let* theta =
       instantiateRight gamma _A1 a1
     in
     instantiateLeft theta a2 (Context.apply theta _A2)
  | PForall (_b, _B) ->
     scoped gamma (CQuantified _b)
       (function gamma -> instantiateLeft gamma _a _B)

and instantiateRight (gamma : Context.t) (_A : poly_t) (_a : string) : (Context.t, [> error]) result =
  let* (gammaL, gammaR) = break_apart_at (CUnsolved _a) gamma in
  let solveRight (_t : mono_t) : (Context.t, [> error]) result =
    let* _ = well_formed_type gammaR _A in
    Ok (List.append gammaL (CSolved (_a, _t) :: gammaR))
  in
  match _A with
  | PLiteral -> solveRight MLiteral
  | PVariable v -> solveRight (MVariable v)
  | PUnsolved _b ->
     ( match break_apart_at (CUnsolved _b) gammaL with
       | Error `FailedToBreakApart ->
          solveRight (MUnsolved _b)
       | Ok (gammaLL, gammaLR) ->
          let gammaL =
            List.append gammaLL (CSolved (_b, MUnsolved _a) :: gammaLR)
          in
          let gamma =
            List.append gammaL (CUnsolved _a :: gammaR)
          in
          Ok gamma
     )
  | PFunction (_A1, _A2) ->
     let a1 = fresh_name () in
     let a2 = fresh_name () in
     let gamma =
       let gammaM =
         [CSolved (_a, MFunction (MUnsolved a1, MUnsolved a2)); CUnsolved a1; CUnsolved a2]
       in
       List.concat [gammaL;gammaM;gammaR]
     in
     let* theta =
       instantiateLeft gamma a1 _A1
     in
     instantiateRight theta (Context.apply theta _A2) a2
  | PForall (_b, _B) ->
     let _b' = fresh_name () in
     scoped_unsolved gamma _b'
       (function gamma -> instantiateLeft gamma _b' (poly_subst _b (PUnsolved _b') _B))

and check (gamma : Context.t) (e : expr_t) (_A: poly_t) : (Context.t, [> error]) result =
  match (e, _A) with
  | ELiteral, PLiteral ->
     Ok gamma
  | EAbstraction (x, e), PFunction (_A1, _A2) ->
     let x' = fresh_name () in
     scoped gamma (CVariable (x', _A1))
       (function gamma -> check gamma (expr_subst x (EVariable x') e) _A2)
  | _, PForall (_a, _A) ->
     let _a' = fresh_name () in
     scoped gamma (CQuantified _a')
       (function gamma -> check gamma e (poly_subst _a (PVariable _a') _A))
  | _ ->
     let* (theta, _B) = synth gamma e in
     subtype theta (Context.apply theta _B) (Context.apply theta _A)

and synth (gamma : Context.t) (e : expr_t) : (Context.t * poly_t, [> error]) result =
  match e with
  | ELiteral ->
     Ok (gamma, PLiteral)
  | EVariable v ->
     let find_variable = function
       | CVariable (v', t) when String.(v = v') -> Some t
       | _ -> None
     in
     ( match List.find_map gamma ~f:find_variable with
       | Some t ->
          Ok (gamma, t)
       | None ->
          Error (`CannotFindVariable (v, gamma))
     )
  | EAbstraction (x, e) ->
     let _a = fresh_name () in
     let _b = fresh_name () in

     let* delta =
       let x' = fresh_name () in
       scoped (CUnsolved _b :: CUnsolved _a :: gamma) (CVariable (x', PUnsolved _a))
         (function gamma -> check gamma (expr_subst x (EVariable x') e) (PUnsolved _b))
     in

     Ok (delta, PFunction (PUnsolved _a, PUnsolved _b))
  | EApplication (f, x) ->
     let* (theta, f_t) = synth gamma f in
     synth_app theta (Context.apply theta f_t) x
  | EAnnotation (e, a) ->
     let* theta = check gamma e a in Ok (theta, a)
  | ELet (x, v, e) ->
     let* (v_theta, v_t) = synth gamma v in
     let x' = fresh_name () in
     let* (e_theta, e_t) =
       synth
         (CVariable (x', v_t) :: v_theta)
         (expr_subst x (EVariable x') e)
     in
     Ok (e_theta, e_t)

and synth_app (gamma : Context.t) (_A : poly_t) (e : expr_t) : (Context.t * poly_t, [> error]) result =
  match _A with
  | PForall (_a, _A) ->
     let _a' = fresh_name () in
     synth_app (CUnsolved _a' :: gamma) (poly_subst _a (PUnsolved _a') _A) e
  | PUnsolved _a ->
     let _a = fresh_name () in
     let _b = fresh_name () in
     let* (gammaL, gammaR) = break_apart_at (CUnsolved _a) gamma in
     let gammaM =
       [ CSolved (_a, MFunction (MUnsolved _a, MUnsolved _b))
       ; CUnsolved _a
       ; CUnsolved _b
       ]
     in
     let gamma = List.concat [gammaL;gammaM;gammaR] in
     let* delta = check gamma e (PUnsolved _a) in
     Ok (delta, PUnsolved _b)
  | PFunction (_A1, _A2) ->
     let* delta = check gamma e _A1 in
     Ok (delta, _A2)
  | _ ->
     Error (`CannotSynthesizeApplication _A)

let infer (e : expr_t) : (poly_t, [> error]) result =
  let* (delta, poly_type) = synth [] e in
  let unsolved =
    let predicate = function
      | CUnsolved u -> Some u
      | _ -> None
    in
    List.filter_map delta ~f:predicate
  in
  let algebra u t =
    PForall (u, poly_subst u (PVariable u) t)
  in
  Ok (List.fold_right unsolved
        ~f:algebra ~init:(Context.apply delta poly_type))
