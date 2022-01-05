(** Expressions in the language.  *)

type 'a t =
  | Literal of ('a t) Literal.t
  | Variable of string
  | Lambda of string * 'a t
  | Apply of 'a t * 'a t
  | Annotate of 'a t * Type.t
  | Let of string * Type.t option * 'a t * 'a t
  [@@deriving eq]

(** [substitute a r e] takes all occurences of the variable a inside of an
    expression e and replaces them with an expression r.
  *)
let rec substitute (a : string) (r : _ t) (e : _ t) : _ t =
  match e with
  | Literal _ -> e
  | Variable a' ->
     if String.equal a a' then r else e
  | Lambda (a', e') ->
     if String.equal a a' then e else Lambda (a', substitute a r e')
  | Apply (f, x) ->
     Apply (substitute a r f, substitute a r x)
  | Annotate (e, t) ->
     Annotate (substitute a r e, t)
  | Let (a', n, e1, e2) ->
     Let
       ( a'
       , n
       , substitute a r e1
       , if String.equal a a' then
           e2
         else
           substitute a r e2
       )
