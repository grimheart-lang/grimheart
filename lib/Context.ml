open Core_kernel
open Syntax

type element_t =
  | CVariable of string * poly_t
  | CQuantified of string
  | CUnsolved of string
  | CSolved of string * mono_t
  | CMarker of string
  [@@deriving eq]

type t = element_t list

type error =
  [ `FailedToBreakApart
  ]

let rec apply (context : t) (poly_type : poly_t) : poly_t =
  match poly_type with
  | PLiteral -> PLiteral
  | PVariable _ -> poly_type
  | PUnsolved unsolved ->
     let find_solved = function
       | CSolved (solved, t) when String.(solved = unsolved) ->
          Some (poly_of_mono t)
       | _ ->
          None
     in
     let solved_type =
       match List.find_map context ~f:find_solved with
       | Some t -> apply context t
       | None -> poly_type
     in
     solved_type
  | PFunction (ar, rt) ->
     PFunction (apply context ar, apply context rt)
  | PForall (qn, ty) ->
     PForall (qn, apply context ty)

let mem (context : t) (element : element_t) : bool =
  List.mem context element ~equal:equal_element_t

let discard_up_to (element : element_t) (context : t) : t =
  let rec aux = function
    | [] -> []
    | current :: rest ->
       if equal_element_t element current then
         rest
       else
         aux rest
  in
  aux context

let break_apart_at (element : element_t) (context : t) : (t * t, [> error]) Result.t =
  let rec aux collected = function
    | [] -> Error `FailedToBreakApart
    | current :: rest ->
       if equal_element_t element current then
         Ok (List.rev collected, rest)
       else
         aux (current :: collected) rest
  in
  aux [] context
