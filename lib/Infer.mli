(** This module contains the type checking and inference algorithm. *)

(** The type of errors thrown in this module. *)
type error =
    [ `CannotFindVariable of string * Context.t
    | `CannotSubtype of Syntax.poly_t * Syntax.poly_t
    | `CannotSynthesizeApplication of Syntax.poly_t
    | `FailedToBreakApart
    | `NotWellFormed of Context.t * Syntax.poly_t
    ]

(** [infer expression] synthesizes the type of some expression, and quantifies
    all unsolved variables to ensure that a polymorphic/generalized type is
    produced.
  *)
val infer : Syntax.expr_t -> (Syntax.poly_t, [> error ]) result
