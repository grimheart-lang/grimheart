(* This module is implemented based on the Algorithmic PolyKinds system
   introduced in Kind Inference for Datatypes. The original paper and its
   technical supplement can be found in these links:

   https://richarde.dev/papers/2020/kind-inference/kind-inference.pdf

   https://arxiv.org/pdf/1911.06153.pdf *)
open Core_kernel
open Sulfur_ast
open Sulfur_errors.Let

let fresh_name : unit -> string =
  let i = ref (-1) in
  fun () ->
    incr i;
    "k" ^ string_of_int !i

let scoped (context : Context.t) (element : Context.Element.t)
    (action : Context.t -> (Context.t, Sulfur_errors.t) result) :
    (Context.t, Sulfur_errors.t) result =
  let* context' = action (element :: context) in
  Ok (Context.discard_up_to element context')

let scoped_unsolved (context : Context.t) (unsolved : string) (kind : Type.t)
    (action : Context.t -> ('a, Sulfur_errors.t) result) :
    ('a, Sulfur_errors.t) result =
  scoped context (Marker unsolved) (fun context ->
      action (KindedUnsolved (unsolved, kind) :: context))

let rec instantiate (_gamma : Context.t) ((_T, _K) : Type.t * Type.t)
    (_K : Type.t) : (Context.t * Type.t, Sulfur_errors.t) result =
  failwith "instantiate: undefined"

and check (_gamma : Context.t) (_T : Type.t) (_K : Type.t) :
    (Context.t * Type.t, Sulfur_errors.t) result =
  failwith "check: undefined"

and infer (_gamma : Context.t) (_T : Type.t) :
    (Context.t * Type.t, Sulfur_errors.t) result =
  failwith "infer: undefined"

and infer_apply (_gamma : Context.t) ((_T, _K) : Type.t * Type.t) (_K : Type.t)
    : (Context.t * Type.t, Sulfur_errors.t) result =
  failwith "infer_apply: undefined"

and elaborate (ctx : Context.t) (_T : Type.t) : (Type.t, Sulfur_errors.t) result
    =
  let open Type.Primitives in
  match _T with
  (* A-ELA-TCON *)
  | Constructor _ when is_primitive_type _T -> Ok t_type
  | Constructor _ when is_primitive_type_type _T ->
      Ok Type.Sugar.(fn t_type t_type)
  | Constructor "Function" -> Ok Type.Sugar.(fn t_type (fn t_type t_type))
  | Constructor _ ->
      raise
        (Failure "Elaborated kind synthesis failed for arbitrary constructors.")
  (* A-ELA-KUVAR *)
  | Unsolved a ->
      let* _, p, _ = Context.break_apart_at_kinded_unsolved a ctx in
      Ok (Context.apply ctx p)
  (* A-ELA-VAR *)
  | Variable a -> (
      let f : Context.Element.t -> _ = function
        | Context.Element.KindedQuantified (a', k) when String.equal a a' ->
            Some k
        | _ -> None
      in
      match List.find_map ctx ~f with
      | Some k -> Ok (Context.apply ctx k)
      | None -> Error (Sulfur_errors.UnknownVariable a))
  (* A-ELA-APP *)
  | Apply (p1, _) -> (
      let* w1_w2 = elaborate ctx p1 in
      match w1_w2 with
      | Apply (Apply (t_function', _), w2)
        when Type.equal t_function t_function' ->
          Ok w2
      | _ -> failwith "todo: add a better error.")
  (* A-ELA-KAPP *)
  | KindApply (p1, p2) -> (
      let* w1 = elaborate ctx p1 in
      match w1 with
      | Forall (a, _, t) -> Ok (Type.substitute a t (Context.apply ctx p2))
      | _ -> failwith "todo: add a better error.")
  (* A-ELA-FORALL *)
  | Forall _ -> Ok t_type
  (* A-ELA-ANNOTATE *)
  | Annotate (_, _K) -> Ok _K

and unify (ctx : Context.t) (_A : Type.t) (_B : Type.t) :
    (Context.t, Sulfur_errors.t) result =
  let open Type.Primitives in
  match (_A, _B) with
  | Apply (Apply (t_function1, a1), b1), Apply (Apply (t_function2, a2), b2)
    when Type.equal t_function t_function1 && Type.equal t_function t_function2
    ->
      let* ctx = unify ctx a2 a1 in
      unify ctx (Context.apply ctx b1) (Context.apply ctx b2)
  | _, Forall (b, k, t) ->
      let b' = fresh_name () in
      let k' = fresh_name () in
      let k = match k with Some k -> k | None -> Unsolved k' in
      let t = Type.substitute b (Unsolved b') t in
      scoped_unsolved ctx k' t_type (fun ctx ->
          scoped_unsolved ctx b' k (fun ctx -> unify ctx _A t))
  | Forall (a, k, t), _ ->
      let a' = fresh_name () in
      let k' = fresh_name () in
      let k = match k with Some k -> k | None -> Unsolved k' in
      let t = Type.substitute a (Unsolved a') t in
      scoped_unsolved ctx k' t_type (fun ctx ->
          scoped_unsolved ctx a' k (fun ctx -> unify ctx t _B))
  (* A-U-APP *)
  | Apply (p1, p2), Apply (p3, p4) ->
      let* gamma = unify ctx p1 p3 in
      unify gamma (Context.apply gamma p2) (Context.apply gamma p4)
  (* A-U-KAPP *)
  | KindApply (p1, p2), KindApply (p3, p4) ->
      let* gamma = unify ctx p1 p3 in
      unify gamma (Context.apply gamma p2) (Context.apply gamma p4)
  (* A-U-REFL-TT *)
  | _A, _B when Type.equal _A _B -> Ok ctx
  (* A-U-KVARL-TT *)
  | Unsolved a, p1 -> unify_unsolved ctx a p1
  (* A-U-KVARR-TT *)
  | p1, Unsolved a -> unify_unsolved ctx a p1
  (* FALLTHROUGH *)
  | _ -> failwith "unify: FALLTHROUGH: todo: raise a more appropriate error"

and promote (ctx : Context.t) (a : string) (_T : Type.t) :
    (Context.t * Type.t, Sulfur_errors.t) result =
  match _T with
  (* A-PR-KUVARL / A-PR-KUVARR-TT *)
  | Unsolved b -> (
      (* Δ[β][α] ~ Δ,β,Δ'[α] ~ Δ,β,Δ',α,Δ'' *)
      (* 1. Break apart the input context with beta into its left and right
         components. *)
      let* ctxR, p, _ = Context.break_apart_at_kinded_unsolved b ctx in
      (* 2. If the right component can be broken apart with alpha, the
         A-PR-KUVARL rule follows. Otherwise, A-PR-KUVARR-TT gets used
         instead. *)
      match Context.break_apart_at_kinded_unsolved a ctxR with
      (* A-PR-KUVARL *)
      | Ok _ -> Ok (ctx, _T)
      (* A-PR-KUVARR-TT *)
      | Error _ ->
          let* ctx, p1 = promote ctx a (Context.apply ctx p) in
          let* _, k, theta = Context.break_apart_at_kinded_unsolved a ctx in
          let b1 = fresh_name () in
          let theta =
            let open Context.Element in
            KindedSolved (b, p, Unsolved b1)
            :: KindedUnsolved (a, k)
            :: KindedUnsolved (b1, p1)
            :: theta
          in
          Ok (theta, Type.Unsolved b1))
  | _ -> Ok (ctx, _T)

and unify_unsolved (ctx : Context.t) (a : string) (p1 : Type.t) :
    (Context.t, Sulfur_errors.t) result =
  let* ctx, p2 = promote ctx a p1 in
  let* ctx2, w1, ctx1 = Context.break_apart_at_kinded_unsolved a ctx in
  let* w2 = elaborate ctx1 p2 in
  let* ctx3 = unify ctx1 (Context.apply ctx1 w1) w2 in
  Ok (List.append ctx2 (Context.Element.KindedSolved (a, w1, p2) :: ctx3))
