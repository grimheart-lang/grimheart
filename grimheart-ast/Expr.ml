open Core_kernel

type 'a t =
  | Literal of 'a t Literal.t
  | Variable of string
  | Lambda of string * 'a t
  | Apply of 'a t * 'a t
  | Annotate of 'a t * Type.t
  | Let of string * Type.t option * 'a t * 'a t
[@@deriving eq, show]

let rec substitute (a : string) (r : _ t) (e : _ t) : _ t =
  match e with
  | Literal _ -> e
  | Variable a' -> if String.equal a a' then r else e
  | Lambda (a', e') ->
      if String.equal a a' then e else Lambda (a', substitute a r e')
  | Apply (f, x) -> Apply (substitute a r f, substitute a r x)
  | Annotate (e, t) -> Annotate (substitute a r e, t)
  | Let (a', n, e1, e2) ->
      Let
        ( a'
        , n
        , substitute a r e1
        , if String.equal a a' then e2 else substitute a r e2 )

module Pretty = struct
  let rec pretty_print : unit t -> string = function
    | Literal (Char c) -> Format.sprintf "%C" c
    | Literal (String s) -> Format.sprintf "%S" s
    | Literal (Int i) -> Format.sprintf "%i" i
    | Literal (Float f) -> Format.sprintf "%f" f
    | Literal (Array xs) ->
        Format.sprintf "[ %s ]"
          (List.map ~f:pretty_print xs |> String.concat ~sep:", ")
    | Literal (Object _) -> failwith "pretty_print: unimplemented"
    | Variable v -> v
    | Lambda (x, e) -> Format.sprintf "λ%s. %s" x (pretty_print e)
    | Apply (a, b) -> Format.sprintf "%s %s" (parenthesize a) (parenthesize b)
    | Annotate (a, b) ->
        Format.sprintf "%s %s" (parenthesize a) (Type.Pretty.pretty_print b)
    | Let (x, t, v, e) ->
        let xt =
          match t with
          | Some t -> Format.sprintf "(%s : %s)" x (Type.Pretty.pretty_print t)
          | None -> x
        in
        Format.sprintf "let %s = %s in %s" xt (pretty_print v) (pretty_print e)

  and parenthesize (a : unit t) : string =
    match a with
    | Apply _ | Annotate _ | Let _ | Lambda _ ->
        Format.sprintf "(%s)" (pretty_print a)
    | _ -> pretty_print a
end
