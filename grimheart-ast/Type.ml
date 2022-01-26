open Core_kernel

type t =
  | Constructor of string
  | Variable of string
  | Unsolved of int
  | Forall of string * t option * t * int option
  | Skolem of string * t option * int * int
  | Apply of t * t
  | KindApply of t * t
  | Annotate of t * t
[@@deriving eq, show]

module Traversal = struct
  let everywhere (fn : t -> t) (t : t) : t =
    let rec aux (t : t) =
      match t with
      | Constructor _ | Variable _ | Unsolved _ | Skolem _ -> fn t
      | Forall (q, k, t, s) -> fn (Forall (q, Option.map ~f:aux k, aux t, s))
      | Apply (a, b) -> fn (Apply (aux a, aux b))
      | KindApply (a, b) -> fn (KindApply (aux a, aux b))
      | Annotate (a, b) -> fn (Annotate (aux a, aux b))
    in
    aux t

  module Monadic (M : Monad.Basic) = struct
    let ( let* ) x f = M.bind ~f x

    let everywhere (fn : t -> t M.t) (t : t) : t M.t =
      let rec aux (t : t) =
        match t with
        | Constructor _ | Variable _ | Unsolved _ | Skolem _ -> fn t
        | Forall (q, k, t, s) -> (
            let* t = aux t in
            match k with
            | Some k ->
                let* k = aux k in
                fn (Forall (q, Some k, t, s))
            | None -> fn (Forall (q, None, t, s)))
        | Apply (a, b) ->
            let* a = aux a in
            let* b = aux b in
            fn (Apply (a, b))
        | KindApply (a, b) ->
            let* a = aux a in
            let* b = aux b in
            fn (KindApply (a, b))
        | Annotate (a, b) ->
            let* a = aux a in
            let* b = aux b in
            fn (Annotate (a, b))
      in
      aux t
  end
end

let type_vars (t : t) : String.Set.t =
  let module Set = String.Set in
  let rec aux (t : t) : Set.t =
    match t with
    | Variable v -> Set.singleton v
    | Forall (_, k, t, _) -> (
        match k with Some k -> Set.union (aux k) (aux t) | None -> aux t)
    | Apply (a, b) | KindApply (a, b) | Annotate (a, b) ->
        Set.union (aux a) (aux b)
    | Constructor _ | Unsolved _ | Skolem _ -> Set.empty
  in
  aux t

let substitute_all (substitutions : (string * t) list) : t -> t =
  let module Map = String.Map in
  let module Set = String.Set in
  let fresh (v : string) (x : Set.t) =
    let rec aux (i : int) =
      let n = Format.sprintf "%s%i" v i in
      if Set.mem x n then aux (i + 1) else n
    in
    aux 0
  in
  let rec aux (qs : Set.t) (st : t Map.t) (t : t) : t =
    match t with
    | Variable v -> ( match String.Map.find st v with Some t -> t | None -> t)
    | Forall (q, k, t, s) when Map.mem st q ->
        let k = Option.map ~f:(aux qs st) k in
        (* Remove q from substitutions before proceeding. *)
        aux (Set.add qs q) (Map.remove st q) (Forall (q, k, t, s))
    | Forall (q, k, t, s) ->
        let possible_collisions =
          Map.data st |> List.map ~f:type_vars |> Set.union_list
        in
        let k' = Option.map ~f:(aux qs st) k in
        (* Rename q if it collides with any of the substitutions. *)
        if Set.mem possible_collisions q
        then
          (* Make sure to not use substitution keys, quantified variables, or
             possible collisions. *)
          let q' =
            fresh q (Set.union_list [Map.key_set st; qs; possible_collisions])
          in
          let t' = aux qs (Map.singleton q (Variable q')) t in
          Forall (q', k', aux (Set.add qs q) st t', s)
          (* Otherwise, do nothing. *)
        else Forall (q, k', aux (Set.add qs q) st t, s)
    | Apply (a, b) -> Apply (aux qs st a, aux qs st b)
    | KindApply (a, b) -> KindApply (aux qs st a, aux qs st b)
    | Annotate (a, b) -> Annotate (aux qs st a, aux qs st b)
    | _ -> t
  in
  aux Set.empty (Map.of_alist_exn substitutions)

let substitute (k : string) (v : t) : t -> t = substitute_all [(k, v)]

module Prim = struct
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
  open Prim

  let fn a b = Apply (Apply (t_function, a), b)

  let ap a b = Apply (a, b)

  let k_ap a b = KindApply (a, b)

  let an a b = Annotate (a, b)

  let forall a t = Forall (a, None, t, None)

  let forall' a k t = Forall (a, Some k, t, None)

  let var a = Variable a

  let uns a = Unsolved a
end

module Pretty = struct
  let pretty_print (t : t) : string =
    let open Prim in
    let rec aux : t -> string = function
      | Constructor n -> n
      | Variable v -> v
      | Unsolved u -> Format.sprintf "t%i?" u
      | Forall (a, k, t, _) ->
          let v =
            match k with
            | Some k -> Format.sprintf "(%s : %s)" a (aux k)
            | None -> a
          in
          Format.sprintf "∀%s. %s" v (aux t)
      | Skolem (s, k, _, _) -> (
          match k with
          | Some k -> Format.sprintf "(%s^ : %s)" s (aux k)
          | None -> s ^ "^")
      | Apply (Apply (t_function', a), b) when equal t_function t_function' ->
          let a =
            match a with
            | Forall _ -> Format.sprintf "(%s)" (aux a)
            | _ -> aux a
          in
          Format.sprintf "%s → %s" a (aux b)
      | Apply (a, b) -> Format.sprintf "%s %s" (parenthesize a) (parenthesize b)
      | KindApply (a, b) ->
          Format.sprintf "%s @%s" (parenthesize a) (parenthesize b)
      | Annotate (a, b) ->
          Format.sprintf "%s : %s" (parenthesize a) (parenthesize b)
    and parenthesize (a : t) : string =
      match a with
      | Annotate _ | KindApply _ | Apply _ | Forall _ ->
          Format.sprintf "(%s)" (aux a)
      | _ -> aux a
    in
    aux t
end
