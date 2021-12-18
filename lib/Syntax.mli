(** This module contains the definitions of types and expressions used in the
    language—as well as operations that can be applied to them.
 *)

type type_vars = Base.Set.M(Core_kernel.String).t

(** The type of monotypes.  *)
type mono_t =
    MLiteral
  | MVariable of string
  | MUnsolved of string
  | MFunction of mono_t * mono_t

val equal_mono_t : mono_t -> mono_t -> bool

(** The type of polytypes. *)
type poly_t =
    PLiteral
  | PVariable of string
  | PUnsolved of string
  | PFunction of poly_t * poly_t
  | PForall of string * poly_t

val equal_poly_t : poly_t -> poly_t -> bool

(** The type of expressions. *)
type expr_t =
    ELiteral
  | EVariable of string
  | EAbstraction of string * expr_t
  | EApplication of expr_t * expr_t
  | EAnnotation of expr_t * poly_t
  | ELet of string * expr_t * expr_t

val equal_expr_t : expr_t -> expr_t -> bool

(** [expr_subst n a b] substitutes all variables n in b with a. *)
val expr_subst : string -> expr_t -> expr_t -> expr_t

(** [mono_subst n a b] substitutes all variables n in b with a. *)
val mono_subst : string -> mono_t -> mono_t -> mono_t

(** [poly_subst n a b] substitutes all variables n in b with a. *)
val poly_subst : string -> poly_t -> poly_t -> poly_t

(** [poly_of_mono m] converts some monotype into a polytype. *)
val poly_of_mono : mono_t -> poly_t

(** [free_type_variables t] collects all variables that are not bound by a
    forall quantifier inside some polytype t.
 *)
val free_type_variables : poly_t -> type_vars
