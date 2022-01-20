open Grimheart_ast
open Grimheart_core_errors

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

module Make : functor (E : Environment.S) -> S
