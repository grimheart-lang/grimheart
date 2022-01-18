open Grimheart_ast

val well_formed_type :
  Context.t -> Type.t -> (unit, Grimheart_core_errors.t) result
(** [well_formed_type context _T] determines the well-formedness of some type _T
    with respect to the context. This function is used to partially verify the
    correctness of the algorithmic context. *)

val subsumes :
  Context.t -> Type.t -> Type.t -> (Context.t, Grimheart_core_errors.t) result
(** [subsumes t1 t2] subsumes t1 with t2. *)

val unify :
  Context.t -> Type.t -> Type.t -> (Context.t, Grimheart_core_errors.t) result
(** [unify t1 t2] unifies t1 with t2. *)

val solve :
  Context.t -> string -> Type.t -> (Context.t, Grimheart_core_errors.t) result
(** [solve a _A] attempts to solve the existential a with the type _A. *)

val check :
     Context.t
  -> unit Expr.t
  -> Type.t
  -> (Context.t, Grimheart_core_errors.t) result
(** [check gamma e _A] checks that the expression e has the type _A. *)

val infer :
     Context.t
  -> unit Expr.t
  -> (Context.t * Type.t, Grimheart_core_errors.t) result
(** [infer gamma e] infers the type of an expression e. *)

val infer_apply :
     Context.t
  -> Type.t
  -> unit Expr.t
  -> (Context.t * Type.t, Grimheart_core_errors.t) result
(** [infer_apply gamma _A e] infers the type of the application of some type _A
    to an expression e. *)

val infer_type_with :
  Context.t -> unit Expr.t -> (Type.t, Grimheart_core_errors.t) result
(** [infer_type_with context e] infers the type of some expression e using the
    provided context. *)

val infer_type : unit Expr.t -> (Type.t, Grimheart_core_errors.t) result
(** [infer_type e] infers the type of some expression with an empty context. *)
