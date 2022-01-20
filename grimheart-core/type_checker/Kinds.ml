(* This module is implemented based on the Algorithmic PolyKinds system
   introduced in Kind Inference for Datatypes. The original paper and its
   technical supplement can be found in these links:

   https://richarde.dev/papers/2020/kind-inference/kind-inference.pdf

   https://arxiv.org/pdf/1911.06153.pdf *)
open Core_kernel
open Grimheart_ast
open Grimheart_core_errors
open Grimheart_core_errors.Let

let should_instantiate : Type.t -> bool = function
  | Forall _ -> true
  | _ -> false

module type S = sig
  val instantiate :
    Context.t -> Type.t * Type.t -> Type.t -> (Context.t * Type.t) result'

  val check : Context.t -> Type.t -> Type.t -> (Context.t * Type.t) result'

  val infer : Context.t -> Type.t -> (Context.t * Type.t * Type.t) result'

  val infer_apply :
       Context.t
    -> Type.t * Type.t
    -> Type.t
    -> (Context.t * Type.t * Type.t) result'

  val elaborate : Context.t -> Type.t -> Type.t result'

  val subsumes : Context.t -> Type.t -> Type.t -> Context.t result'

  val unify : Context.t -> Type.t -> Type.t -> Context.t result'

  val promote : Context.t -> string -> Type.t -> (Context.t * Type.t) result'

  val unify_unsolved : Context.t -> string -> Type.t -> Context.t result'
end

module Make (E : Environment.S) : S = struct
  let fresh_name : unit -> string =
    let i = ref (-1) in
    fun () ->
      incr i;
      "k" ^ string_of_int !i

  let rec instantiate (ctx : Context.t) ((t1, k1) : Type.t * Type.t)
      (k2 : Type.t) : (Context.t * Type.t) result' =
    match k1 with
    (* A-INST_FORALL *)
    | Forall (a, Some k, t) when not @@ should_instantiate k2 ->
        let u = fresh_name () in
        instantiate
          (KindedUnsolved (u, k) :: ctx)
          (KindApply (t1, Unsolved u), Type.substitute a (Unsolved u) t)
          k2
    (* A-INST-REFL *)
    | _ ->
        let* ctx = subsumes ctx k1 k2 in
        Ok (ctx, t1)

  and check (ctx : Context.t) (t : Type.t) (w : Type.t) :
      (Context.t * Type.t) result' =
    (* A-KC-SUB *)
    let* ctx, t, k = infer ctx t in
    instantiate ctx (t, Context.apply ctx w) (Context.apply ctx k)

  and infer (ctx : Context.t) (t : Type.t) :
      (Context.t * Type.t * Type.t) result' =
    let open Type.Primitives in
    match t with
    (* A-KTT-CON *)
    | Constructor _ when is_primitive_type t -> Ok (ctx, t, t_type)
    | Constructor _ when is_primitive_type_type t ->
        Ok (ctx, t, Type.Sugar.fn t_type t_type)
    | Constructor "Function" ->
        Ok (ctx, t, Type.Sugar.(fn t_type (fn t_type t_type)))
    | Constructor n -> (
        match E.find n with
        | Some t -> Ok (ctx, t, Context.apply ctx t)
        (* todo: add a different error. *)
        | None -> Error (UnknownVariable n))
    (* A-KTT-VAR *)
    | Variable a -> (
        let f : Context.Element.t -> _ = function
          | Context.Element.KindedQuantified (a', k) when String.equal a a' ->
              Some k
          | _ -> None
        in
        match List.find_map ctx ~f with
        | Some k -> Ok (ctx, t, Context.apply ctx k)
        | None -> Error (Grimheart_core_errors.UnknownVariable a))
    (* A-KTT-SKOLEM *)
    | Skolem (_, k) -> (
        match k with
        | Some k -> Ok (ctx, t, Context.apply ctx k)
        | None ->
            Error
              (InternalKindCheckerError "infer: skolem variable has no kind."))
    (* A-KTT-KUVAR *)
    | Unsolved u ->
        let* _, k, _ = Context.break_apart_at_kinded_unsolved u ctx in
        Ok (ctx, t, k)
    (* A-KTT-FORALL *)
    | Forall (a, Some k, t) ->
        let* ctx, k = check ctx k t_type in
        let* ctx, t = check (KindedQuantified (a, k) :: ctx) t t_type in
        let* ctx3, ctx2 =
          Context.break_apart_at (KindedQuantified (a, k)) ctx
        in
        Ok
          ( List.append (Context.unsolved ctx3) ctx2
          , Type.Forall (a, Some k, Context.apply ctx3 t)
          , t_type )
    (* A-KTT-FORALLI *)
    | Forall (a, None, t) ->
        let u = fresh_name () in
        let* ctx, t =
          check
            (KindedQuantified (a, Unsolved u)
            :: KindedUnsolved (u, t_type)
            :: ctx)
            t t_type
        in
        let* ctx3, ctx2 =
          Context.break_apart_at (KindedQuantified (a, Unsolved u)) ctx
        in
        Ok
          ( List.append (Context.unsolved ctx3) ctx2
          , Type.Forall (a, Some (Unsolved u), Context.apply ctx3 t)
          , t_type )
    (* A-KTT-APP *)
    | Apply (t1, t2) ->
        let* ctx, t1, k1 = infer ctx t1 in
        infer_apply ctx (t1, Context.apply ctx k1) t2
    (* A-KTT-KAPP *)
    | KindApply (t1, t2) -> (
        let* ctx, t1, k1 = infer ctx t1 in
        match Context.apply ctx k1 with
        | Forall (a, Some k, t) ->
            let* ctx, t2 = check ctx t2 k in
            Ok (ctx, Type.KindApply (t1, t2), Type.substitute a t2 t)
        | _ ->
            let message =
              Printf.sprintf
                "infer: kind application is invalid for %s. It must be a \
                 forall with a kind annotation."
                (Type.show t1)
            in
            Error (InternalKindCheckerError message))
    (* A-KTT-ANNOTATE *)
    | Annotate (t1, t2) ->
        let* ctx, t2, _ = infer ctx t2 in
        let* ctx, t1 = check ctx t1 t2 in
        Ok (ctx, t1, Context.apply ctx t2)

  and infer_apply (ctx : Context.t) ((fn, fnKind) : Type.t * Type.t)
      (ar : Type.t) : (Context.t * Type.t * Type.t) result' =
    let open Type.Primitives in
    match fnKind with
    (* A-KAPP-FORALL *)
    | Forall (a, Some k, t) ->
        let u = fresh_name () in
        infer_apply
          (KindedUnsolved (u, k) :: ctx)
          (KindApply (fn, Unsolved u), Type.substitute a (Unsolved u) t)
          ar
    (* A-KAPP-TT-KUVAR *)
    | Unsolved u ->
        let u1 = fresh_name () in
        let u2 = fresh_name () in
        let* ctx2, k, ctx1 = Context.break_apart_at_kinded_unsolved u ctx in
        let ctx =
          let ctx1_2 =
            let open Context.Element in
            [
              KindedSolved (u, k, Type.Sugar.fn (Unsolved u1) (Unsolved u2))
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
    | _ -> Error (CouldNotApplyKind (fn, fnKind, ar))

  and elaborate (ctx : Context.t) (_T : Type.t) : Type.t result' =
    let open Type.Primitives in
    match _T with
    | Skolem (_, k) -> (
        match k with
        | Some k -> Ok (Context.apply ctx k)
        | None ->
            Error (InternalKindCheckerError "elaborate: skolem has no kind."))
    (* A-ELA-TCON *)
    | Constructor _ when is_primitive_type _T -> Ok t_type
    | Constructor _ when is_primitive_type_type _T ->
        Ok Type.Sugar.(fn t_type t_type)
    | Constructor "Function" -> Ok Type.Sugar.(fn t_type (fn t_type t_type))
    | Constructor _ ->
        raise
          (Failure
             "Elaborated kind synthesis failed for arbitrary constructors.")
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
        | None -> Error (Grimheart_core_errors.UnknownVariable a))
    (* A-ELA-APP *)
    | Apply (p1, _) -> (
        let* w1_w2 = elaborate ctx p1 in
        match w1_w2 with
        | Apply (Apply (t_function', _), w2)
          when Type.equal t_function t_function' ->
            Ok w2
        | _ ->
            let message =
              Printf.sprintf
                "elaborate: expecting %s to elaborate to a function, got %s \
                 instead."
                (Type.show p1) (Type.show w1_w2)
            in
            Error (InternalKindCheckerError message))
    (* A-ELA-KAPP *)
    | KindApply (p1, p2) -> (
        let* w1 = elaborate ctx p1 in
        match w1 with
        | Forall (a, _, t) -> Ok (Type.substitute a t (Context.apply ctx p2))
        | _ ->
            let message =
              Printf.sprintf
                "elaborate: expecting %s to elaborate to a forall, got %s \
                 instead."
                (Type.show p1) (Type.show w1)
            in
            Error (InternalKindCheckerError message))
    (* A-ELA-FORALL *)
    | Forall _ -> Ok t_type
    (* A-ELA-ANNOTATE *)
    | Annotate (_, _K) -> Ok _K

  and subsumes (ctx : Context.t) (t1 : Type.t) (t2 : Type.t) : Context.t result'
      =
    let open Type.Primitives in
    match (t1, t2) with
    | Apply (Apply (t_function1, a1), b1), Apply (Apply (t_function2, a2), b2)
      when Type.equal t_function t_function1
           && Type.equal t_function t_function2 ->
        let* ctx = subsumes ctx a2 a1 in
        subsumes ctx (Context.apply ctx b1) (Context.apply ctx b2)
    | _, Forall (b, k, t) ->
        let b' = fresh_name () in
        let t = Type.substitute b (Skolem (b', k)) t in
        let m =
          match k with
          | Some k -> Context.Element.KindedQuantified (b', k)
          | None -> Context.Element.Quantified b'
        in
        Context.scoped ctx m (fun ctx -> subsumes ctx t1 t)
    | Forall (a, k, t), _ -> (
        let a' = fresh_name () in
        let t = Type.substitute a (Unsolved a') t in
        match k with
        | Some k ->
            Context.scoped_kinded_unsolved ctx a' k (fun ctx ->
                subsumes ctx t t2)
        | None ->
            let k' = fresh_name () in
            Context.scoped_kinded_unsolved ctx k' t_type (fun ctx ->
                Context.scoped_kinded_unsolved ctx a' (Unsolved k') (fun ctx ->
                    subsumes ctx t t2)))
    | _ -> unify ctx t1 t2

  and unify (ctx : Context.t) (t1 : Type.t) (t2 : Type.t) : Context.t result' =
    match (t1, t2) with
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
    | _A, _B -> Error (CouldNotUnifyKinds (_A, _B))

  and promote (ctx : Context.t) (a : string) (t : Type.t) :
      (Context.t * Type.t) result' =
    match t with
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
        | Ok (_, _, ctxL) ->
            let* _ = Context.well_formed_type ctxL t in
            Ok (ctx, t)
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
    | _ ->
        let* _, _, ctxL = Context.break_apart_at_kinded_unsolved a ctx in
        let* _ = Context.well_formed_type ctxL t in
        Ok (ctx, t)

  and unify_unsolved (ctx : Context.t) (a : string) (p1 : Type.t) :
      Context.t result' =
    let* ctx, p2 = promote ctx a p1 in
    let* ctx2, w1, ctx1 = Context.break_apart_at_kinded_unsolved a ctx in
    let* w2 = elaborate ctx1 p2 in
    let* ctx3 = unify ctx1 (Context.apply ctx1 w1) w2 in
    Ok (List.append ctx2 (Context.Element.KindedSolved (a, w1, p2) :: ctx3))
end
