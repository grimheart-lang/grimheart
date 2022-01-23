open Core_kernel
open Grimheart_ast

module Hints = struct
  type t =
    | SubsumingTypes of Type.t * Type.t
    | UnifyingTypes of Type.t * Type.t
    | CheckingType of unit Expr.t * Type.t
    | InferringType of unit Expr.t
    | UnifyingKinds of Type.t * Type.t
    | CheckingKind of Type.t * Type.t
    | InferringKind of Type.t
  [@@deriving eq, show]
end

module Message = struct
  type t =
    | CouldNotUnifyTypes of Type.t * Type.t
    | CouldNotInferType of unit Expr.t
    | CouldNotApplyTypeOn of Type.t * unit Expr.t
    | CouldNotUnifyKinds of Type.t * Type.t
    | CouldNotApplyKindOn of Type.t * Type.t * Type.t
    | EscapedSkolemVariable of Type.t
    | TypeVariableNotInScope of Type.t
    | UnknownVariable of string
    | UnknownConstructor of string
    | InternalError of string
  [@@deriving eq, show]
end

type t = HintedError of Hints.t list * Message.t [@@deriving eq, show]

type 'a result' = ('a, t) Result.t

let with_message (message : Message.t) : t = HintedError ([], message)

let add_hint (hint : Hints.t) = function
  | HintedError (hints, message) -> HintedError (hint :: hints, message)

let with_hint (hint : Hints.t) : 'a result' -> 'a result' =
  Result.map_error ~f:(add_hint hint)

module Let = struct
  let ( let* ) : 'a result' -> _ = Result.( >>= )

  let ( and* ) : 'a result' -> _ = Result.Let_syntax.Let_syntax.both
end

module Pretty = struct
  module E = Expr.Pretty
  module T = Type.Pretty

  let pretty_print_hint : Hints.t -> string = function
    | SubsumingTypes (a, b) ->
        sprintf "while subsuming the type\n  %s with %s" (T.pretty_print a)
          (T.pretty_print b)
    | UnifyingTypes (a, b) ->
        sprintf "while unifying the type\n  %s with %s" (T.pretty_print a)
          (T.pretty_print b)
    | CheckingType (a, b) ->
        sprintf "while checking that the expression \n  %s has type %s"
          (E.pretty_print a) (T.pretty_print b)
    | InferringType a ->
        sprintf "while inferring the expression\n  %s" (E.pretty_print a)
    | UnifyingKinds (a, b) ->
        sprintf "while unifying kinds\n  %s with %s" (T.pretty_print a)
          (T.pretty_print b)
    | CheckingKind (a, b) ->
        sprintf "while checking\n  %s type has kind %s" (T.pretty_print a)
          (T.pretty_print b)
    | InferringKind a ->
        sprintf "while inferring kind of\n  %s" (T.pretty_print a)

  let pretty_print_message : Message.t -> string = function
    | CouldNotUnifyTypes (a, b) ->
        sprintf "could not unify type\n\n  %s\n\nwith type\n\n  %s"
          (T.pretty_print a) (T.pretty_print b)
    | CouldNotInferType e ->
        sprintf "could not infer type of\n\n  %s" (E.pretty_print e)
    | CouldNotApplyTypeOn (a, b) ->
        sprintf "could not apply type\n\n  %s\n\nto expression\n\n  %s"
          (T.pretty_print a) (E.pretty_print b)
    | CouldNotUnifyKinds (a, b) ->
        sprintf "could not unify kind\n\n  %s\n\nwith kind\n\n  %s"
          (T.pretty_print a) (T.pretty_print b)
    | CouldNotApplyKindOn (a, b, c) ->
        sprintf "could not apply kind\n\n  %s : %s\n\nwith kind\n\n  %s"
          (T.pretty_print a) (T.pretty_print b) (T.pretty_print c)
    | EscapedSkolemVariable v ->
        sprintf "escaped skolem variable %s" (T.pretty_print v)
    | TypeVariableNotInScope v ->
        sprintf "type variable not in scope %s" (T.pretty_print v)
    | UnknownVariable n -> sprintf "unknown name %s" n
    | UnknownConstructor c -> sprintf "unknown constructor %s" c
    | InternalError m -> sprintf "internal error: %s" m

  let pretty_print : t -> string = function
    | HintedError (hints, message) ->
        sprintf "\nan error occurred:\n\n%s\n\n%s\n"
          (pretty_print_message message)
          (List.map ~f:pretty_print_hint hints |> String.concat ~sep:"\n\n")
end
