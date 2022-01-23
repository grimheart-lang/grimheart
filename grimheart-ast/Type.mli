type type_vars_t = Core_kernel.Set.M(Core_kernel.String).t

(** The type of types in the language. *)
type t =
  | Constructor of string
  | Variable of string
  | Skolem of string * t option
  | Unsolved of string
  | Forall of string * t option * t
  | Apply of t * t
  | KindApply of t * t
  | Annotate of t * t

val equal : t -> t -> bool

val pp : Format.formatter -> t -> unit

val show : t -> string

val substitute : string -> t -> t -> t
(** [substitute a r t] takes all occurences of the variable a inside of a type t
    and replaces them with the type r. This is essentially just alpha conversion
    for types. *)

val is_mono_type : t -> bool
(** [is_mono_type t] determines whether some type t is a monotype. *)

val free_type_variables : t -> type_vars_t
(** [free_type_variables t] determines the free type variables in some type t. *)

(** Primitive types in the language. *)
module Primitives : sig
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

(** Syntax sugar for writing types. *)
module Sugar : sig
  val fn : t -> t -> t
  (** Smart constructor for creating functions. *)

  val ap : t -> t -> t
  (** Smart constructor for creating applications. *)

  val k_ap : t -> t -> t
  (** Smart constructor for creating kind applications. *)

  val an : t -> t -> t
  (** Smart constructor for creating annotations. *)

  val forall : string -> t -> t
  (** Smart constructor for foralls. *)

  val forall' : string -> t -> t -> t
  (** Smart constructor for kinded foralls. *)

  val var : string -> t
  (** Smart constructor for variables. *)

  val uns : string -> t
  (** Smart constructor for unsolved variables. *)
end

module Pretty : sig
  val pretty_print : t -> string
end
