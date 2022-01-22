(** Type-checking context. *)
open Core_kernel

open Grimheart_ast
open Grimheart_core_errors
open Grimheart_core_errors.Let

module Element = struct
  type t =
    | Quantified of string
    | Unsolved of string
    | Solved of string * Type.t
    | KindedQuantified of string * Type.t
    | KindedUnsolved of string * Type.t
    | KindedSolved of string * Type.t * Type.t
    | Marker of string
  [@@deriving eq, show]
end

type t = Element.t list [@@deriving eq, show]

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
    | [] ->
        Error (with_message (InternalError "Could not break context apart."))
    | current :: rest ->
        if Element.equal element current
        then Ok (List.rev collected, rest)
        else aux (current :: collected) rest
  in
  aux [] context

let break_apart_at_unsolved (a : string) (context : t) :
    (t * t, Grimheart_core_errors.t) result =
  let rec aux (collected : t) : t -> (t * t, _) result = function
    | [] ->
        Error (with_message (InternalError "Could not break context apart."))
    | Unsolved a' :: rest when String.equal a a' -> Ok (List.rev collected, rest)
    | current :: rest -> aux (current :: collected) rest
  in
  aux [] context

let break_apart_at_kinded_unsolved (a : string) (context : t) :
    (t * Type.t * t, Grimheart_core_errors.t) result =
  let rec aux (collected : t) : t -> (t * Type.t * t, _) result = function
    | [] ->
        Error (with_message (InternalError "Could not break context apart."))
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

let rec well_formed_type (context : t) (t : Type.t) :
    (unit, Grimheart_core_errors.t) result =
  match t with
  | Constructor _ -> Ok ()
  | Skolem (v, k) ->
      let f : Element.t -> bool = function
        | Quantified v' when String.equal v v' -> true
        | KindedQuantified (v', k')
          when String.equal v v'
               && (Option.equal Type.equal k (Some k')
                  || Option.equal Type.equal k None) ->
            true
        | _ -> false
      in
      if Option.is_some @@ List.find ~f context
      then Ok ()
      else Error (with_message (EscapedSkolemVariable t))
  | Variable v ->
      let f : Element.t -> bool = function
        | Quantified v' when String.equal v v' -> true
        | KindedQuantified (v', _) when String.equal v v' -> true
        | _ -> false
      in
      if Option.is_some @@ List.find ~f context
      then Ok ()
      else Error (with_message (TypeVariableNotInScope t))
  | Unsolved u ->
      let f : Element.t -> bool = function
        | Unsolved u'
        | KindedUnsolved (u', _)
        | Solved (u', _)
        | KindedSolved (u', _, _)
          when String.equal u u' ->
            true
        | _ -> false
      in
      if Option.is_some @@ List.find ~f context
      then Ok ()
      else Error (with_message (TypeVariableNotInScope t))
  | Forall (a, k, _A) -> (
      match k with
      | Some k -> well_formed_type (KindedQuantified (a, k) :: context) _A
      | None -> well_formed_type (Quantified a :: context) _A)
  | Apply (_A, _B) | KindApply (_A, _B) | Annotate (_A, _B) ->
      let* _ = well_formed_type context _A
      and* _ = well_formed_type context _B in
      Ok ()

let scoped (context : t) (element : Element.t)
    (action : t -> (t, Grimheart_core_errors.t) result) :
    (t, Grimheart_core_errors.t) result =
  let* context' = action (element :: context) in
  Ok (discard_up_to element context')

let scoped_unsolved (context : t) (unsolved : string)
    (action : t -> ('a, Grimheart_core_errors.t) result) :
    ('a, Grimheart_core_errors.t) result =
  scoped context (Marker unsolved) (fun context ->
      action (Unsolved unsolved :: context))

let scoped_kinded_unsolved (context : t) (unsolved : string) (kind : Type.t)
    (action : t -> ('a, Grimheart_core_errors.t) result) :
    ('a, Grimheart_core_errors.t) result =
  scoped context (Marker unsolved) (fun context ->
      action (KindedUnsolved (unsolved, kind) :: context))
