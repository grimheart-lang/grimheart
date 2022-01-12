(** The type of context elements. *)
module Element : sig
  type t =
    | Variable of string * Type.t
    | Quantified of string * Type.t option
    | Unsolved of string
    | Solved of string * Type.t
    | Marker of string

  val equal : t -> t -> bool
end

(** The type of the context. *)
type t = Element.t list

(** The error type used in this module. *)
module Error : sig
  type t = FailedToBreakApart

  val equal : t -> t -> bool

  val pp : Format.formatter -> t -> unit

  val show : t -> string
end

val apply : t -> Type.t -> Type.t
(** [apply context _T] applies a context to a type _T. This takes all unsolved
    variables and tries to solve them with respect to the provided context. *)

val mem : t -> Element.t -> bool
(** [mem context element] checks whether an element is a member of the context. *)

val discard_up_to : Element.t -> t -> t
(** [discard_up_to element context] discards all elements up to the provided
    element in the provided context. *)

val break_apart_at : Element.t -> t -> (t * t, Error.t) result
(** [break_apart_at element context] breaks the context to its left and right
    components relative to the provided element. *)
