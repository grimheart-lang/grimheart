open Sulfur_ast

val well_formed_type : Context.t -> Type.t -> (unit, Errors.t) result
(** [well_formed_type context _T] determines the well-formedness of some type _T
    with respect to the context. This function is used to partially verify the
    correctness of the algorithmic context. *)

val unify : Context.t -> Type.t -> Type.t -> (Context.t, Errors.t) result
(** [subtype _A _B] unifies the type _A with _B. *)

val instantiate : Context.t -> string -> Type.t -> (Context.t, Errors.t) result
(** [instantiate a _A] instantiates the unsolved variable a with _B. *)

val check : Context.t -> unit Expr.t -> Type.t -> (Context.t, Errors.t) result
(** [check gamma e _A] checks that the expression e has the type _A. *)

val infer : Context.t -> unit Expr.t -> (Context.t * Type.t, Errors.t) result
(** [infer gamma e] infers the type of an expression e. *)

val infer_apply :
  Context.t -> Type.t -> unit Expr.t -> (Context.t * Type.t, Errors.t) result
(** [infer_apply gamma _A e] infers the type of the application of some type _A
    to an expression e. *)

val check_kind : Context.t -> Type.t -> Type.t -> (Context.t, Errors.t) result
(** [check_kind gamma _T _K] checks whether some type _T has a kind _K. *)

val infer_kind : Context.t -> Type.t -> (Context.t * Type.t, Errors.t) result
(** [infer_kind gamma _T] infers the kind of some type _T. *)

val infer_apply_kind :
  Context.t -> Type.t -> Type.t -> (Context.t * Type.t, Errors.t) result
(** [infer_apply_kind gamma _K _X] infers the type of the application of the
    kind _K to some type _X. *)

val infer_type_with : Context.t -> unit Expr.t -> (Type.t, Errors.t) result
(** [infer_type_with context e] infers the type of some expression e using the
    provided context. *)

val infer_type : unit Expr.t -> (Type.t, Errors.t) result
(** [infer_type e] infers the type of some expression with an empty context. *)
