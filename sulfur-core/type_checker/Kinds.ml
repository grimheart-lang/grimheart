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

let should_instantiate : Type.t -> bool = function
  | Forall _ -> true
  | _ -> false

let rec instantiate (ctx : Context.t) ((_T, _K) : Type.t * Type.t) (_L : Type.t)
    : (Context.t * Type.t, Sulfur_errors.t) result =
  match _K with
  (* A-INST_FORALL *)
  | Forall (a, Some k, t) when should_instantiate _L ->
      let k' = fresh_name () in
      instantiate
        (KindedUnsolved (k', k) :: ctx)
        (KindApply (_T, Unsolved k'), Type.substitute a (Unsolved k') t)
        _L
  (* A-INST-REFL *)
  | _ ->
      let* ctx = unify ctx _K _L in
      Ok (ctx, _T)

and check (ctx : Context.t) (_T : Type.t) (_K : Type.t) :
    (Context.t * Type.t, Sulfur_errors.t) result =
  (* A-KC-SUB *)
  let* ctx, _T', _K' = infer ctx _T in
  instantiate ctx (_T', Context.apply ctx _K) (Context.apply ctx _K')

and infer (ctx : Context.t) (_T : Type.t) :
    (Context.t * Type.t * Type.t, Sulfur_errors.t) result =
  let open Type.Primitives in
  match _T with
  (* A-KTT-CON *)
  | Constructor _ when is_primitive_type _T -> Ok (ctx, _T, t_type)
  | Constructor _ when is_primitive_type_type _T ->
      Ok (ctx, _T, Type.Sugar.fn t_type t_type)
  | Constructor "Function" ->
      Ok (ctx, _T, Type.Sugar.(fn t_type (fn t_type t_type)))
  | Constructor _ ->
      raise (Failure "Kind synthesis failed for arbitrary constructors.")
  (* A-KTT-VAR *)
  | Variable a -> (
      let f : Context.Element.t -> _ = function
        | Context.Element.KindedQuantified (a', k) when String.equal a a' ->
            Some k
        | _ -> None
      in
      match List.find_map ctx ~f with
      | Some k -> Ok (ctx, _T, Context.apply ctx k)
      | None -> Error (Sulfur_errors.UnknownVariable a))
  (* A-KTT-KUVAR *)
  | Unsolved u ->
      let* _, k, _ = Context.break_apart_at_kinded_unsolved u ctx in
      Ok (ctx, _T, k)
  (* A-KTT-FORALL *)
  | Forall (a, Some k, t) ->
      let* ctx, k = check ctx k t_type in
      let* ctx, t = check (KindedQuantified (a, k) :: ctx) t t_type in
      let* ctx3, ctx2 = Context.break_apart_at (KindedQuantified (a, k)) ctx in
      let unsolved =
        let f : Context.Element.t -> bool = function
          | Unsolved _ -> true
          | KindedUnsolved _ -> true
          | _ -> false
        in
        List.filter ctx3 ~f
      in
      Ok
        ( List.append unsolved ctx2
        , Type.Forall (a, Some k, Context.apply ctx3 t)
        , t_type )
  (* A-KTT-FORALLI *)
  | Forall (a, None, t) ->
      let u = fresh_name () in
      let* ctx, t =
        check
          (KindedQuantified (a, Unsolved u) :: KindedUnsolved (u, t_type) :: ctx)
          t t_type
      in
      let* ctx3, ctx2 =
        Context.break_apart_at (KindedQuantified (a, Unsolved u)) ctx
      in
      let unsolved =
        let f : Context.Element.t -> bool = function
          | Unsolved _ -> true
          | KindedUnsolved _ -> true
          | _ -> false
        in
        List.filter ctx3 ~f
      in
      Ok
        ( List.append unsolved ctx2
        , Type.Forall (a, Some (Unsolved u), Context.apply ctx3 t)
        , t_type )
  (* A-KTT-APP *)
  | Apply (t1, t2) ->
      let* ctx, t1, k1 = infer ctx t1 in
      infer_apply ctx (t1, k1) t2
  (* A-KTT-KAPP *)
  | KindApply (t1, t2) -> (
      let* ctx, t1, k1 = infer ctx t1 in
      let t1 = Context.apply ctx t1 in
      match k1 with
      | Forall (a, Some k, t) ->
          let* ctx, t2 = check ctx t2 k in
          Ok (ctx, Type.KindApply (t1, t2), Type.substitute a t2 t)
      | _ -> failwith "infer: Forall has no kind")
  (* A-KTT-ANNOTATE *)
  | Annotate (t1, t2) ->
      let* ctx, t2, _ = infer ctx t2 in
      let* ctx, t1 = check ctx t1 t2 in
      Ok (ctx, t1, Context.apply ctx t2)

and infer_apply (ctx : Context.t) ((fn, fnKind) : Type.t * Type.t) (ar : Type.t)
    : (Context.t * Type.t * Type.t, Sulfur_errors.t) result =
  let open Type.Primitives in
  match fnKind with
  (* A-KAPP-FORALL *)
  | Forall (a, Some w, t) ->
      let u = fresh_name () in
      infer_apply
        (KindedUnsolved (u, w) :: ctx)
        (KindApply (fn, Unsolved u), Type.substitute a (Unsolved u) t)
        ar
  (* A-KAPP-TT-KUVAR *)
  | Unsolved u ->
      let u1 = fresh_name () in
      let u2 = fresh_name () in
      let* ctx2, w, ctx1 = Context.break_apart_at_kinded_unsolved u ctx in
      let ctx =
        let ctx1_2 =
          let open Context.Element in
          [
            KindedSolved (u, w, Type.Sugar.fn (Unsolved u1) (Unsolved u2))
          ; KindedUnsolved (u2, t_type)
          ; KindedUnsolved (u1, t_type)
          ]
        in
        List.concat [ctx2; ctx1_2; ctx1]
      in
      let* ctx, ar = check ctx ar (Unsolved u1) in
      Ok (ctx, Type.Apply (fn, ar), Type.Unsolved u2)
  (* A-KAPP-TT-ARROW *)
  | Apply (Apply (t_function', arKind), rtKind)
    when Type.equal t_function t_function' ->
      let* ctx, t = check ctx ar arKind in
      Ok (ctx, Type.Apply (fn, t), Context.apply ctx rtKind)
  | _ -> failwith "infer_apply: todo: add a better error"

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
