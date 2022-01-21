open Core_kernel
open Grimheart_ast

type t = (string, Type.t) Hashtbl.t

module type S = sig
  val environment : t

  val find : string -> Type.t option

  val insert : key:string -> data:Type.t -> unit

  val delete : string -> unit

  val temporarily : key:string -> data:Type.t -> (unit -> 'a) -> 'a
end

module Make () : S = struct
  let environment = Hashtbl.create (module String)

  let find = Hashtbl.find environment

  let insert = Hashtbl.set environment

  let delete = Hashtbl.remove environment

  let temporarily ~key ~data callback =
    insert ~key ~data;
    let result = callback () in
    delete key;
    result
end
