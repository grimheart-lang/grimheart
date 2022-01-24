open Core_kernel
open Grimheart_ast

module type S = sig
  module Names : Grimheart_utils.Map.S_Make(String)(Type).S

  module Types : Grimheart_utils.Map.S_Make(String)(Type).S
end

module Make () : S = struct
  module Names = Grimheart_utils.Map.Make (String) (Type)
  module Types = Grimheart_utils.Map.Make (String) (Type)
end
