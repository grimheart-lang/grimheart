let unknown : unit -> int =
  let i = ref (-1) in
  fun () ->
    incr i;
    !i

let skolem : unit -> int =
  let i = ref (-1) in
  fun () ->
    incr i;
    !i
