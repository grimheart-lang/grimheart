(** This module contains the definition of an ordered context used in the type
    checking and type inference algorithm—as well as various helper operations.
 *)

(** The type of context elements. *)
type element_t =
    CVariable of string * Syntax.poly_t
  | CQuantified of string
  | CUnsolved of string
  | CSolved of string * Syntax.mono_t
  | CMarker of string

val equal_element_t : element_t -> element_t -> bool

(** The type of the context—an ordered collection of {!element_t}
    items representing a stack.
  *)
type t = element_t list

(** The type of errors thrown in this module.  *)
type error = [ `FailedToBreakApart ]

(** [apply context poly_type] replaces each {!Syntax.PUnsolved} in
    poly_type with its corresponding {!CSolved} entry in the context.
 *)
val apply : t -> Syntax.poly_t -> Syntax.poly_t

(** [mem context element] checks if an element appears inside a context. *)
val mem : t -> element_t -> bool

(** [discard_up_to element context] removes elements at the top of the context
    stack up to the specified element.
    {[ # discard_up_to (CMarker "a") [_1, _2, CMarker "a", _3, _4]
       [_3, _4]
    ]}
  *)
val discard_up_to : element_t -> t -> t

(** [break_apart_at element context] returns the left and right components of a
    context with the specified element as the pivot.
    {[ # break_apart_at (CMarker "a") [_1, _2, CMarker "a", _3, _4]
       ( [_1, _2]
       , [_3, _4]
       )
    ]}
 *)
val break_apart_at : element_t -> t -> (t * t, [> error ]) result
