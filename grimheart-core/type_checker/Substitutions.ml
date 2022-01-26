open Core_kernel
open Grimheart_ast

module UnsolvedIndex = struct
  module T = struct
    type t = int * int list [@@deriving sexp]

    let compare ((x, xs) : t) ((y, ys) : t) : int =
      let augment : int * int -> int = function
        | -1, _ -> -1
        | 0, y -> y
        | 1, _ -> 1
        | _ -> failwith "Invalid value."
      in
      let rec aux (xs : int list) (ys : int list) =
        match (xs, ys) with
        | [], [] -> 0
        | _, [] -> -1
        | [], _ -> 1
        | x :: xs, y :: ys -> augment (Int.compare x y, aux xs ys)
      in
      aux (x :: xs) (y :: ys)
  end

  include T
  include Comparable.Make (T)
end

module type S = sig
  module Types : Grimheart_utils.Map.S_Make(Int)(Type).S

  module Unsolved :
    Grimheart_utils.Map.S_Make(Int)(Tuple.Make(UnsolvedIndex)(Type)).S
end

module Make () : S = struct
  module Types = Grimheart_utils.Map.Make (Int) (Type)
  module Unsolved =
    Grimheart_utils.Map.Make (Int) (Tuple.Make (UnsolvedIndex) (Type))
end
