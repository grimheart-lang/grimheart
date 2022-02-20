open Core_kernel

module type S = sig
  type value

  type t = value Map.M(String).t

  val contents : t ref

  val find : string -> value option

  val set : string -> value -> unit

  val bracketed : (unit -> 'a) -> 'a
end

module type I = sig
  type value
end

module Make (M : I) : S with type value = M.value = struct
  type value = M.value

  type t = value Map.M(String).t

  let contents : t ref = ref (Map.empty (module String))

  let find (key : string) : value option = Map.find !contents key

  let set (key : string) (data : value) : unit =
    contents := Map.set ~key ~data !contents

  let bracketed (action : unit -> 'a) : 'a =
    let pre_contents = !contents in
    let result = action () in
    contents := pre_contents;
    result
end
