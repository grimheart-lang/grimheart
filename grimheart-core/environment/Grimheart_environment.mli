open Core_kernel
open Grimheart_ast

module type S = sig
  (** The {!Map} instance of term-related names to {!Grimheart_ast.Type.t} s *)
  module Names : Grimheart_utils.Map.S_Make(String)(Type).S

  (** The {!Map} instance of type-related names to {!Grimheart_ast.Type.t} s *)
  module Types : Grimheart_utils.Map.S_Make(String)(Type).S
end

module Make () : S
