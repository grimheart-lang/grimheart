open Grimheart_ast
open Grimheart_utils

module type S = sig
  module Values : Map.S with type value = Type.t

  module Types : Map.S with type value = Type.t
end

module Make () : S = struct
  module Values = Map.Make (struct
    type value = Type.t
  end)

  module Types = Map.Make (struct
    type value = Type.t
  end)
end
