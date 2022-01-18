(** Type-checking context. *)
open Core_kernel

open Grimheart_ast
open Grimheart_core_errors

module Element = struct
  type t =
    | Variable of string * Type.t
    | Quantified of string
    | Unsolved of string
    | Solved of string * Type.t
    | KindedQuantified of string * Type.t
    | KindedUnsolved of string * Type.t
    | KindedSolved of string * Type.t * Type.t
    | Marker of string
  [@@deriving eq]
end

type t = Element.t list

let rec apply (context : t) (t : Type.t) : Type.t =
  let open Type in
  match t with
  | Constructor _ -> t
  | Variable _ -> t
  | Skolem (a, k) -> (
      match k with Some k -> Skolem (a, Some (apply context k)) | None -> t)
  | Unsolved u ->
      let find_solved = function
        | (Element.Solved (u', t) | Element.KindedSolved (u', _, t))
          when String.equal u u' ->
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
    (t * t, Grimheart_core_errors.t) result =
  let rec aux (collected : t) : t -> (t * t, _) result = function
    | [] -> Error FailedToBreakApart
    | current :: rest ->
        if Element.equal element current
        then Ok (List.rev collected, rest)
        else aux (current :: collected) rest
  in
  aux [] context

let break_apart_at_unsolved (a : string) (context : t) :
    (t * t, Grimheart_core_errors.t) result =
  let rec aux (collected : t) : t -> (t * t, _) result = function
    | [] -> Error FailedToBreakApart
    | Unsolved a' :: rest when String.equal a a' -> Ok (List.rev collected, rest)
    | current :: rest -> aux (current :: collected) rest
  in
  aux [] context

let break_apart_at_kinded_unsolved (a : string) (context : t) :
    (t * Type.t * t, Grimheart_core_errors.t) result =
  let rec aux (collected : t) : t -> (t * Type.t * t, _) result = function
    | [] -> Error FailedToBreakApart
    | KindedUnsolved (a', k) :: rest when String.equal a a' ->
        Ok (List.rev collected, k, rest)
    | current :: rest -> aux (current :: collected) rest
  in
  aux [] context

let unsolved : t -> t =
  let f : Element.t -> bool = function
    | Unsolved _ | KindedUnsolved _ -> true
    | _ -> false
  in
  List.filter ~f
