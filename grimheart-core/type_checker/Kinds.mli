open Grimheart_ast

module type S = sig
  val instantiate :
       Context.t
    -> Type.t * Type.t
    -> Type.t
    -> (Context.t * Type.t, Grimheart_errors.t) result
  (** [instantiate context (t1, k1) k2] instantiates the type t1, with its kind
      k1, such that k1 eventually subsumes k2, and t1 is layered with kind
      applications. *)

  val check :
       Context.t
    -> Type.t
    -> Type.t
    -> (Context.t * Type.t, Grimheart_errors.t) result
  (** [check context t k] checks that the type t has the kind k. *)

  val infer :
       Context.t
    -> Type.t
    -> (Context.t * Type.t * Type.t, Grimheart_errors.t) result
  (** [infer context t] infers the kind of the type t. *)

  val infer_apply :
       Context.t
    -> Type.t * Type.t
    -> Type.t
    -> (Context.t * Type.t * Type.t, Grimheart_errors.t) result
  (** [infer_apply context (fn, fnKind) ar] infers the kind of the application
      of the type fn, with its kind fnKind, to the type ar. *)

  val elaborate : Context.t -> Type.t -> (Type.t, Grimheart_errors.t) result
  (** [elaborate context t] elaborates the type t to obtain its kind. *)

  val subsumes :
    Context.t -> Type.t -> Type.t -> (Context.t, Grimheart_errors.t) result
  (** [subsumes context t1 t2] subsumes t1 with t2, defaulting to unification. *)

  val unify :
    Context.t -> Type.t -> Type.t -> (Context.t, Grimheart_errors.t) result
  (** [unify context t1 t2] unifies t1 with t2. *)

  val promote :
       Context.t
    -> string
    -> Type.t
    -> (Context.t * Type.t, Grimheart_errors.t) result
  (** [promote context a t] promotes an unsolved variable a to eventually solve
      to the type t.

      This is used when unifying unsolved variables with other types, and
      functions similarly to the [solve] routine in the type checker. *)

  val unify_unsolved :
    Context.t -> string -> Type.t -> (Context.t, Grimheart_errors.t) result
  (** [unify_unsolved context a t] unifies the unsolved variable a with the type
      t. *)
end

module Make : functor (E : Grimheart_environment.S) -> S
