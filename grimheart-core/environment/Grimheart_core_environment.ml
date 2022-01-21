open Core_kernel
open Grimheart_ast

module Map = struct
  module type S = sig
    type value

    type t = value Map.M(String).t

    val contents : t ref

    val find : string -> value option

    module Mutable : sig
      val bracketed : (unit -> 'a) -> 'a

      val set : string -> value -> unit
    end
  end

  module type I = sig
    type value
  end

  module Make (M : I) : S with type value = M.value = struct
    type value = M.value

    type t = value Map.M(String).t

    let contents : t ref = ref (Map.empty (module String))

    let find (key : string) : value option = Map.find !contents key

    module Mutable = struct
      let bracketed (action : unit -> 'a) : 'a =
        let pre_contents = !contents in
        let result = action () in
        contents := pre_contents;
        result

      let set (key : string) (data : value) : unit =
        contents := Map.set ~key ~data !contents
    end
  end
end

module type S = sig
  module Names : Map.S with type value = Type.t

  module Types : Map.S with type value = Type.t
end

module Make () = struct
  module Names = Map.Make (struct
    type value = Type.t
  end)

  module Types = Map.Make (struct
    type value = Type.t
  end)
end

(* let () = *)
(*   let open Make () in *)
(*   let open Type.Sugar in *)
(*   print_endline @@ [%derive.show: Type.t option] (Types.find "id"); *)
(*   Types.Mutable.bracketed (fun () -> *)
(*       let open Types.Mutable in *)
(*       set "id" (forall "a" @@ fn (var "id") (var "id")); *)
(*       print_endline @@ [%derive.show: Type.t option] (Types.find "id")); *)
(*   print_endline @@ [%derive.show: Type.t option] (Types.find "id") *)
