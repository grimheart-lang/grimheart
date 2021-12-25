open Core_kernel

type type_vars = Set.M(String).t

type mono_t =
  | MUnit
  | MVariable of string
  | MUnsolved of string
  | MFunction of mono_t * mono_t
  [@@deriving eq]

type poly_t =
  | PUnit
  | PVariable of string
  | PUnsolved of string
  | PFunction of poly_t * poly_t
  | PForall of string * poly_t
  [@@deriving eq]

type expr_t =
  | EUnit
  | EVariable of string
  | EAbstraction of string * expr_t
  | EApplication of expr_t * expr_t
  | EAnnotation of expr_t * poly_t
  | ELet of string * poly_t option * expr_t * expr_t
  [@@deriving eq]

let rec expr_subst (expected : string) (replacement : expr_t) (original : expr_t) : expr_t =
  match original with
  | EUnit -> EUnit
  | EVariable x ->
     if String.(x = expected) then
       replacement
     else
       original
  | EAbstraction (x, e) ->
     if String.(x = expected) then
       original
     else
       EAbstraction (x, expr_subst expected replacement e)
  | EApplication (f, e) ->
     EApplication
       ( expr_subst expected replacement f
       , expr_subst expected replacement e
       )
  | EAnnotation (e, t) ->
     EAnnotation (expr_subst expected replacement e, t)
  | ELet (x, a, v, e) ->
     ELet
       ( x
       , a
       , expr_subst expected replacement v
       , if String.(x = expected) then
           e
         else
           expr_subst expected replacement e
       )

let rec mono_subst (expected : string) (replacement : mono_t) (original : mono_t) : mono_t =
  match original with
  | MUnit -> MUnit
  | MVariable v ->
     if String.(v = expected) then
       replacement
     else
       original
  | MUnsolved u ->
     if String.(u = expected) then
       replacement
     else
       original
  | MFunction (a, b) ->
     MFunction
       ( mono_subst expected replacement a
       , mono_subst expected replacement b
       )

let rec poly_subst (expected : string) (replacement : poly_t) (original : poly_t) : poly_t =
  match original with
  | PUnit -> PUnit
  | PVariable v ->
     if String.(v = expected) then
       replacement
     else
       original
  | PUnsolved u ->
     if String.(u = expected) then
       replacement
     else
       original
  | PFunction (a, b) ->
     PFunction
       ( poly_subst expected replacement a
       , poly_subst expected replacement b
       )
  | PForall (a, t) ->
     if String.(a = expected) then
       original
     else
       PForall (a, poly_subst expected replacement t)

let rec poly_of_mono : mono_t -> poly_t = function
  | MUnit -> PUnit
  | MVariable v -> PVariable v
  | MUnsolved v -> PUnsolved v
  | MFunction (a, b) -> PFunction (poly_of_mono a, poly_of_mono b)

let rec free_type_variables : poly_t -> type_vars = function
  | PUnit -> Set.empty (module String)
  | PVariable v -> Set.singleton (module String) v
  | PUnsolved u -> Set.singleton (module String) u
  | PFunction (a, b) -> Set.union (free_type_variables a) (free_type_variables b)
  | PForall (a, b) -> Set.remove (free_type_variables b) a
