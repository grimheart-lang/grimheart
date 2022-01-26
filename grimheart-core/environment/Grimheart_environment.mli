open Core_kernel
open Grimheart_ast

(** A [Map] is a mutable store of [string] names to [value] types. *)
module Map : sig
  (** The signature of a [Map] instance. *)
  module type S = sig
    (** The type of values in the store. *)
    type value

    (** The internal type of the {!Map} instance. *)
    type t = value Map.M(String).t

    val contents : t ref
    (** The contents of the {!Map} instance. *)

    val find : string -> value option
    (** [find key] looks up a [key] in the [Map] and returns a [value option]. *)

    (** Module for mutable {!Map} operations. *)
    module Mutable : sig
      val bracketed : (unit -> 'a) -> 'a
      (** [bracketed action] saves the current state of the [Map], performs some
          [action], and restores the saved state. *)

      val set : string -> value -> unit
      (** [set key value] overrides a [key] in the {!Map} with a [value]. *)
    end
  end

  (** The inputs of a {!Map} instance. *)
  module type I = sig
    (** The type of values in the store. *)
    type value
  end

  (** The constructor for a {!Map} instance. Takes an input {!I} and creates an
      {!S} with a specialized [value].

      {[
        module Types = Map.Make (struct
          type value = Type.t
        end)
      ]} *)
  module Make : functor (M : I) -> S with type value = M.value
end

(** The signature of the [Environment] instance. *)
module type S = sig
  (** The {!Map} instance of term-related names to {!Grimheart_ast.Type.t} s *)
  module Names : Map.S with type value = Type.t

  (** The {!Map} instance of type-related names to {!Grimheart_ast.Type.t} s *)
  module Types : Map.S with type value = Type.t
end

(** The constructor for an [Environment] instance. *)
module Make () : S
