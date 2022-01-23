(** The type of expressions in the language. *)
type 'a t =
  | Literal of 'a t Literal.t
  | Variable of string
  | Lambda of string * 'a t
  | Apply of 'a t * 'a t
  | Annotate of 'a t * Type.t
  | Let of string * Type.t option * 'a t * 'a t

val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit

val show : (Format.formatter -> 'a -> unit) -> 'a t -> string

val substitute : string -> 'a t -> 'a t -> 'a t
(** [substitute a r e] takes all occurences of the variable a inside of an
    expression e and replaces them with an expression r. *)

module Pretty : sig
  val pretty_print : unit t -> string
end
