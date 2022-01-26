open Grimheart_ast

module type S = sig
  val subsumes :
    Context.t -> Type.t -> Type.t -> (Context.t, Grimheart_errors.t) result
  (** [subsumes context t1 t2] subsumes t1 with t2, defaulting to unification. *)

  val unify :
    Context.t -> Type.t -> Type.t -> (Context.t, Grimheart_errors.t) result
  (** [unify context t1 t2] unifies t1 with t2. *)

  val solve :
    Context.t -> string -> Type.t -> (Context.t, Grimheart_errors.t) result
  (** [solve context a t] solves the unsolved variable a with the type t. *)

  val check :
    Context.t -> unit Expr.t -> Type.t -> (Context.t, Grimheart_errors.t) result
  (** [check context e t] checks that the expression e has the type t. *)

  val infer :
    Context.t -> unit Expr.t -> (Context.t * Type.t, Grimheart_errors.t) result
  (** [infer gamma e] infers the type of the expression e. *)

  val infer_apply :
       Context.t
    -> Type.t
    -> unit Expr.t
    -> (Context.t * Type.t, Grimheart_errors.t) result
  (** [infer_apply gamma t e] infers the type of the application of some type t
      to an expression e. *)

  val infer_type_with :
    Context.t -> unit Expr.t -> (Type.t, Grimheart_errors.t) result
  (** [infer_type_with context e] infers the type of the expression e, given a
      context. *)

  val infer_type : unit Expr.t -> (Type.t, Grimheart_errors.t) result
  (** [infer_type e] infers the type of the expression e with an empty context. *)
end

module Make : functor (E : Grimheart_environment.S) (K : Kinds.S) -> S
