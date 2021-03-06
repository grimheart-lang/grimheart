(** Types in the language. *)
open Core_kernel

type type_vars_t = Set.M(String).t

type t =
  | Constructor of string
  | Variable of string
  | Skolem of string * t option
  | Unsolved of string
  | Forall of string * t option * t
  | Apply of t * t
  | KindApply of t * t
  | Annotate of t * t
[@@deriving eq, show]

let rec substitute (a : string) (r : t) (t : t) : t =
  match t with
  | Constructor _ -> t
  | Variable a' | Skolem (a', _) | Unsolved a' ->
      if String.equal a a' then r else t
  | Forall (a', k, t) ->
      if String.equal a a' then t else Forall (a', k, substitute a r t)
  | Apply (t1, t2) -> Apply (substitute a r t1, substitute a r t2)
  | KindApply (t1, t2) -> KindApply (substitute a r t1, substitute a r t2)
  | Annotate (t1, t2) -> Annotate (substitute a r t1, substitute a r t2)

let is_mono_type (t : t) : bool = match t with Forall _ -> false | _ -> true

let rec free_type_variables (t : t) : type_vars_t =
  match t with
  | Constructor _ -> Set.empty (module String)
  | Variable v | Skolem (v, _) | Unsolved v -> Set.singleton (module String) v
  | Forall (a, _, t) -> Set.remove (free_type_variables t) a
  | Apply (t1, t2) | KindApply (t1, t2) | Annotate (t1, t2) ->
      Set.union (free_type_variables t1) (free_type_variables t2)

module Primitives = struct
  let t_type = Constructor "Type"

  let t_char = Constructor "Char"

  let t_string = Constructor "String"

  let t_int = Constructor "Int"

  let t_float = Constructor "Float"

  let t_array = Constructor "Array"

  let t_function = Constructor "Function"

  let is_primitive_type n =
    List.mem [t_type; t_char; t_string; t_int; t_float] n ~equal

  let is_primitive_type_type n = List.mem [t_array] n ~equal
end

module Sugar = struct
  open Primitives

  let fn a b = Apply (Apply (t_function, a), b)

  let ap a b = Apply (a, b)

  let k_ap a b = KindApply (a, b)

  let an a b = Annotate (a, b)

  let forall a t = Forall (a, None, t)

  let forall' a k t = Forall (a, Some k, t)

  let var a = Variable a

  let uns a = Unsolved a
end
