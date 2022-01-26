type t =
  | Constructor of string
  | Variable of string
  | Unsolved of int
  | Forall of string * t option * t * int option
  | Skolem of string * t option * int * int
  | Apply of t * t
  | KindApply of t * t
  | Annotate of t * t

val equal : t -> t -> bool

val pp : Format.formatter -> t -> unit

val show : t -> string

val type_vars : t -> Core_kernel.String.Set.t

val substitute : string -> t -> t -> t

val substitute_all : (string * t) list -> t -> t

module Traversal : sig
  val everywhere : (t -> t) -> t -> t

  module Monadic : functor
    (T : sig
       type 'a t

       val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
     end)
    -> sig
    val ( let* ) : 'a T.t -> ('a -> 'b T.t) -> 'b T.t

    val everywhereM : (t -> t T.t) -> t -> t T.t
  end
end

module Prim : sig
  val t_type : t

  val t_char : t

  val t_string : t

  val t_int : t

  val t_float : t

  val t_array : t

  val t_function : t

  val is_primitive_type : t -> bool

  val is_primitive_type_type : t -> bool
end

module Sugar : sig
  val fn : t -> t -> t

  val ap : t -> t -> t

  val k_ap : t -> t -> t

  val an : t -> t -> t

  val forall : string -> t -> t

  val forall' : string -> t -> t -> t

  val var : string -> t

  val uns : int -> t
end

module Pretty : sig
  val pretty_print : t -> string
end
