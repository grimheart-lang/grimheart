open Core_kernel
open Grimheart_ast

type t = (string, Type.t) Hashtbl.t

module type S = sig
  val environment : t

  val find : string -> Type.t option
end

module Make () : S = struct
  let environment = Hashtbl.create (module String)

  let find = Hashtbl.find environment
end
