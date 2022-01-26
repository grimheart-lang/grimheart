open Core_kernel
open Grimheart_ast
open Grimheart_core_errors
open Grimheart_core_errors.Let

module type S = sig
  val subsumes : Type.t -> Type.t -> (unit, Grimheart_core_errors.t) result

  val unify : Type.t -> Type.t -> (unit, Grimheart_core_errors.t) result

  val check : unit Expr.t -> Type.t -> (unit, Grimheart_core_errors.t) result

  val infer : unit Expr.t -> (Type.t, Grimheart_core_errors.t) result

  val infer_apply :
    Type.t -> unit Expr.t -> (Type.t, Grimheart_core_errors.t) result
end

module Make (E : Grimheart_core_environment.S) (S : Substitutions.S) : S =
struct
  open Type.Prim

  let apply (t : Type.t) : Type.t =
    let rec aux (t : Type.t) : Type.t =
      match t with
      | Unsolved u -> (
          match S.Types.find u with
          | Some (Unsolved u') when Int.equal u u' -> Unsolved u'
          | Some t -> aux t
          | _ -> t)
      | _ -> t
    in
    Type.Traversal.everywhere aux t

  let fresh_unknown_type_with_kind : Type.t -> Type.t =
    let i = ref (-1) in
    fun kind ->
      incr i;
      let t = Type.Unsolved !i in
      S.Unsolved.set !i ((!i, []), kind);
      t

  let fresh_skolem_constant : unit -> int =
    let i = ref (-1) in
    fun () ->
      incr i;
      !i

  let check_infinite_type (u : int) (t : Type.t) :
      (unit, Grimheart_core_errors.t) result =
    match (u, t) with
    | _, Unsolved _ -> Ok ()
    | _ ->
        let module T = Type.Traversal.Monadic (struct
          type 'a t = ('a, Grimheart_core_errors.t) result

          let ( let* ) = Grimheart_core_errors.Let.( let* )
        end) in
        let aux (t : Type.t) =
          match t with
          | Unsolved u' when Int.equal u u' ->
              Error (with_message (InternalError "Infinite type."))
          | _ -> Ok t
        in
        let* _ = T.everywhereM aux t in
        Ok ()

  let rec subsumes (t1 : Type.t) (t2 : Type.t) :
      (unit, Grimheart_core_errors.t) result =
    with_hint (SubsumingTypes (t1, t2))
    @@
    match (t1, t2) with
    | Apply (Apply (t_function1, a1), b1), Apply (Apply (t_function2, a2), b2)
      when Type.equal t_function t_function1
           && Type.equal t_function t_function2 ->
        let* () = subsumes a2 a1 in
        subsumes (apply b1) (apply b2)
    | Forall (q, k, t1, _), _ -> (
        match k with
        | Some k ->
            let un = fresh_unknown_type_with_kind k in
            let t1 = Type.substitute q un t1 in
            subsumes t1 t2
        | None ->
            Error
              (with_message
                 (InternalError "unify: can't subsume forall without kind")))
    | _, Forall (q, k, t2, s) -> (
        match s with
        | Some s ->
            let ct = fresh_skolem_constant () in
            let t2 = Type.substitute q (Skolem (q, k, ct, s)) t2 in
            subsumes t1 t2
        | None ->
            Error
              (with_message
                 (InternalError "unify: can't subsume forall without scope")))
    | _ -> unify t1 t2

  and unify (t1 : Type.t) (t2 : Type.t) : (unit, Grimheart_core_errors.t) result
      =
    with_hint (UnifyingTypes (t1, t2))
    @@
    match (t1, t2) with
    | Constructor a, Constructor b when String.equal a b -> Ok ()
    | Variable a, Variable b when String.equal a b -> Ok ()
    | Skolem (_, _, a, _), Skolem (_, _, b, _) when Int.equal a b -> Ok ()
    | Forall (q1, k1, t1, s1), Forall (q2, k2, t2, s2) -> (
        match (s1, s2) with
        | Some s1, Some s2 ->
            let ct = fresh_skolem_constant () in
            let t1 = Type.substitute q1 (Skolem (q1, k1, ct, s1)) t1 in
            let t2 = Type.substitute q2 (Skolem (q1, k2, ct, s2)) t2 in
            unify t1 t2
        | _ ->
            Error
              (with_message
                 (InternalError "unify: can't unify foralls without scopes")))
    | Forall (q, k, t1, s), _ -> (
        match s with
        | Some s ->
            let ct = fresh_skolem_constant () in
            let t1 = Type.substitute q (Skolem (q, k, ct, s)) t1 in
            unify t1 t2
        | None ->
            Error
              (with_message
                 (InternalError "unify: can't unify foralls without scopes")))
    | _, Forall (q, k, t2, s) -> (
        match s with
        | Some s ->
            let ct = fresh_skolem_constant () in
            let t2 = Type.substitute q (Skolem (q, k, ct, s)) t2 in
            unify t1 t2
        | None ->
            Error
              (with_message
                 (InternalError "unify: can't unify foralls without scopes")))
    | Unsolved a, Unsolved b when Int.equal a b -> Ok ()
    | Unsolved a, _ -> solve a t2
    | _, Unsolved a -> solve a t1
    | Apply (a1, a2), Apply (b1, b2) ->
        let* () = unify a1 b1 in
        unify a2 b2
    | KindApply (_, a2), KindApply (_, b2) -> unify a2 b2
    | Annotate (t1, _), t2 -> unify t1 t2
    | t1, Annotate (t2, _) -> unify t1 t2
    | _ -> Error (with_message (CouldNotUnifyTypes (t1, t2)))

  and check (_e : unit Expr.t) (_t : Type.t) :
      (unit, Grimheart_core_errors.t) result =
    failwith "check: undefined"

  and infer (_e : unit Expr.t) : (Type.t, Grimheart_core_errors.t) result =
    failwith "infer: undefined"

  and infer_apply (_t : Type.t) (_e : unit Expr.t) :
      (Type.t, Grimheart_core_errors.t) result =
    failwith "infer_apply: undefined"

  and solve (u : int) (t : Type.t) : (unit, Grimheart_core_errors.t) result =
    let* () = check_infinite_type u t in Ok (S.Types.set u t)
end
