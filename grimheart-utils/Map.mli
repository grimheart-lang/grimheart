(** A small wrapper against [Core]'s [Map] type with strings as keys. Also
    supports bracketed operations. *)
open Core_kernel

(** The signature of a [Map] instance. *)
module type S = sig
  (** The type of the values in the store. *)
  type value

  (** The internal type of the [Map] instance. *)
  type t = value Map.M(Core_kernel.String).t

  val contents : t ref
  (** The contents of the [Map] instance. *)

  val find : string -> value option
  (** [find key] looks up a [key] in the [Map] and returns a [value option]. *)

  val set : string -> value -> unit
  (** [set key value] sets a [key] in the [Map] with a [value]. *)

  val bracketed : (unit -> 'a) -> 'a
  (** [bracketed action] saves the current state of the [Map], performs some
      [action], and restores the state. *)
end

(** The signature of a [Map]'s input module. *)
module type I = sig
  (** The type of the values in the store. *)
  type value
end

(** The constructor for a [Map] instance. *)
module Make : functor (M : I) -> S with type value = M.value
