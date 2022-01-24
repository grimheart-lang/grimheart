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

module Make (Env : Grimheart_core_environment.S) (Sub : Substitutions.S) : S =
struct
  open Type.Primitives

  let apply (_t : Type.t) : Type.t = failwith "apply : to implement"

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
    | _ -> unify t1 t2

  and unify (_t1 : Type.t) (_t2 : Type.t) :
      (unit, Grimheart_core_errors.t) result =
    failwith "unify: undefined"

  and check (_e : unit Expr.t) (_t : Type.t) :
      (unit, Grimheart_core_errors.t) result =
    failwith "check: undefined"

  and infer (_e : unit Expr.t) : (Type.t, Grimheart_core_errors.t) result =
    failwith "infer: undefined"

  and infer_apply (_t : Type.t) (_e : unit Expr.t) :
      (Type.t, Grimheart_core_errors.t) result =
    failwith "infer_apply: undefined"
end
