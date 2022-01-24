open Core_kernel

module type Value_S = sig
  type t
end

module S_Make (K : Comparable.S) (V : Value_S) = struct
  module type S = sig
    type t

    val find : K.t -> V.t option

    val bracketed : (unit -> 'a) -> 'a

    val set : K.t -> V.t -> unit
  end
end

module Make (K : Comparable.S) (V : Value_S) : S_Make(K)(V).S = struct
  type t = V.t K.Map.t

  let contents : t ref = ref K.Map.empty

  let find (key : K.t) : V.t option = K.Map.find !contents key

  let set (key : K.t) (data : V.t) : unit =
    contents := K.Map.set ~key ~data !contents

  let bracketed (action : unit -> 'a) : 'a =
    let pre_contents = !contents in
    let result = action () in
    contents := pre_contents;
    result
end
