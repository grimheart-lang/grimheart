(** Type-checking context. *)
open Core_kernel

open Sulfur_ast
open Sulfur_errors

module Element = struct
  type t =
    | Variable of string * Type.t
    | Quantified of string * Type.t option
    | Unsolved of string
    | Solved of string * Type.t
    | Marker of string
  [@@deriving eq]
end

type t = Element.t list

let rec apply (context : t) (t : Type.t) : Type.t =
  let open Type in
  match t with
  | Constructor _ -> t
  | Variable _ -> t
  | Unsolved u ->
      let find_solved = function
        | Element.Solved (u', t) when String.equal u u' ->
            if Type.is_mono_type t
            then Some t
            else
              raise (Failure "A solved type in the context is not a monotype.")
        | _ -> None
      in
      let solved_type =
        match List.find_map context ~f:find_solved with
        | Some t -> apply context t
        | None -> t
      in
      solved_type
  | Forall (a, k, t) ->
      Forall (a, Option.map ~f:(apply context) k, apply context t)
  | Apply (t1, t2) -> Apply (apply context t1, apply context t2)
  | KindApply (t1, t2) -> KindApply (apply context t1, apply context t2)
  | Annotate (t1, t2) -> Annotate (apply context t1, apply context t2)

let mem (context : t) (element : Element.t) : bool =
  List.mem context element ~equal:Element.equal

let discard_up_to (element : Element.t) (context : t) : t =
  let rec aux = function
    | [] -> []
    | current :: rest ->
        if Element.equal element current then rest else aux rest
  in
  aux context

let break_apart_at (element : Element.t) (context : t) :
    (t * t, Sulfur_errors.t) result =
  let rec aux collected = function
    | [] -> Error FailedToBreakApart
    | current :: rest ->
        if Element.equal element current
        then Ok (List.rev collected, rest)
        else aux (current :: collected) rest
  in
  aux [] context
