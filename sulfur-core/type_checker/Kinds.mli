open Sulfur_ast

val check_kind : Context.t -> Type.t -> Type.t -> (Context.t, Sulfur_errors.t) result
