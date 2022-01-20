open Grimheart_ast

(** The type of context elements. *)
module Element : sig
  type t =
    | Variable of string * Type.t
    | Quantified of string
    | Unsolved of string
    | Solved of string * Type.t
    | KindedQuantified of string * Type.t
    | KindedUnsolved of string * Type.t
    | KindedSolved of string * Type.t * Type.t
    | Marker of string

  val equal : t -> t -> bool

  val pp : Format.formatter -> t -> unit

  val show : t -> string
end

(** The type of the context. *)
type t = Element.t list

val equal : t -> t -> bool

val pp : Format.formatter -> t -> unit

val show : t -> string

val apply : t -> Type.t -> Type.t
(** [apply context _T] applies a context to a type _T. This takes all unsolved
    variables and tries to solve them with respect to the provided context. *)

val mem : t -> Element.t -> bool
(** [mem context element] checks whether an element is a member of the context. *)

val discard_up_to : Element.t -> t -> t
(** [discard_up_to element context] discards all elements up to the provided
    element in the provided context. *)

val break_apart_at : Element.t -> t -> (t * t, Grimheart_core_errors.t) result
(** [break_apart_at_unsolved element context] breaks the context to its left and
    right components relative to an element. *)

val break_apart_at_unsolved :
  string -> t -> (t * t, Grimheart_core_errors.t) result
(** [break_apart_at_unsolved unsolved context] breaks the context to its left
    and right components relative to an unsolved variable. *)

val break_apart_at_kinded_unsolved :
  string -> t -> (t * Grimheart_ast.Type.t * t, Grimheart_core_errors.t) result
(** [break_apart_at_kinded_unsolved unsolved context] breaks the context to its
    left and right components relative to an unsolved variable, and also returns
    its kind. *)

val unsolved : t -> t
(** [unsolved context] collects all unsolved elements in some context. *)

val well_formed_type :
  t -> Grimheart_ast.Type.t -> (unit, Grimheart_core_errors.t) result
(** [well_formed_type context type_] asserts the well-formedness of the type
    with respect to the current context. *)

val scoped :
     t
  -> Element.t
  -> (t -> (t, Grimheart_core_errors.t) result)
  -> (t, Grimheart_core_errors.t) result

val scoped_unsolved :
     t
  -> string
  -> (t -> (t, Grimheart_core_errors.t) result)
  -> (t, Grimheart_core_errors.t) result

val scoped_kinded_unsolved :
     t
  -> string
  -> Grimheart_ast.Type.t
  -> (t -> (t, Grimheart_core_errors.t) result)
  -> (t, Grimheart_core_errors.t) result
