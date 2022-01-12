(** Literals in the language. *)

type 'a t =
  | Char of char
  | String of string
  | Int of int
  | Float of float
  | Array of 'a list
  | Object of string * 'a list
[@@deriving eq]
