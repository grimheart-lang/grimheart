open Grimheart_ast
open Grimheart_utils

(** The signature of an [Environment] instance. *)
module type S = sig
  (** The mapping of known values. *)
  module Values : Map.S with type value = Type.t

  (** The mapping of known types. *)
  module Types : Map.S with type value = Type.t
end

(** The constructor for an [Environment] instance. *)
module Make () : S
