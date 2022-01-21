open Core_kernel
open Grimheart_ast

module Member = struct
  type t = (string, Type.t) Hashtbl.t

  module type S = sig
    val contents : t

    val find : string -> Type.t option

    val set : string -> Type.t -> unit

    val remove : string -> unit

    val temporarily : string -> Type.t -> (unit -> 'a) -> 'a
  end

  module Make () : S = struct
    let contents = Hashtbl.create (module String)

    let find = Hashtbl.find contents

    let set key data = Hashtbl.set contents ~key ~data

    let remove = Hashtbl.remove contents

    let temporarily key data callback =
      match find key with
      | Some old_data ->
          set key data;
          let result = callback () in
          set key old_data;
          result
      | None ->
          set key data;
          let result = callback () in
          remove key;
          result
  end
end

module type S = sig
  module Terms : Member.S

  module Types : Member.S
end

module Make () : S = struct
  module Terms = Member.Make ()

  module Types = Member.Make ()
end
