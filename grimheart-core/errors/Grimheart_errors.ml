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

  module Pretty = struct
    let pretty_print : t -> string = function
      | SubsumingTypes (a, b) ->
          sprintf "while subsuming the type\n  %s with %s"
            (Type.Pretty.pretty_print a)
            (Type.Pretty.pretty_print b)
      | UnifyingTypes (a, b) ->
          sprintf "while unifying the type\n  %s with %s"
            (Type.Pretty.pretty_print a)
            (Type.Pretty.pretty_print b)
      | CheckingType (a, b) ->
          sprintf "while checking that the expression \n  %s has type %s"
            (Expr.Pretty.pretty_print a)
            (Type.Pretty.pretty_print b)
      | InferringType a ->
          sprintf "while inferring the expression\n  %s"
            (Expr.Pretty.pretty_print a)
      | UnifyingKinds (a, b) ->
          sprintf "while unifying kinds\n  %s with %s"
            (Type.Pretty.pretty_print a)
            (Type.Pretty.pretty_print b)
      | CheckingKind (a, b) ->
          sprintf "while checking\n  %s type has kind %s"
            (Type.Pretty.pretty_print a)
            (Type.Pretty.pretty_print b)
      | InferringKind a ->
          sprintf "while inferring kind of\n  %s" (Type.Pretty.pretty_print a)
  end
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

  module Pretty = struct
    let pretty_print : t -> string = function
      | CouldNotUnifyTypes (a, b) ->
          sprintf "could not unify type\n\n  %s\n\nwith type\n\n  %s"
            (Type.Pretty.pretty_print a)
            (Type.Pretty.pretty_print b)
      | CouldNotInferType e ->
          sprintf "could not infer type of\n\n  %s" (Expr.Pretty.pretty_print e)
      | CouldNotApplyTypeOn (a, b) ->
          sprintf "could not apply type\n\n  %s\n\nto expression\n\n  %s"
            (Type.Pretty.pretty_print a)
            (Expr.Pretty.pretty_print b)
      | CouldNotUnifyKinds (a, b) ->
          sprintf "could not unify kind\n\n  %s\n\nwith kind\n\n  %s"
            (Type.Pretty.pretty_print a)
            (Type.Pretty.pretty_print b)
      | CouldNotApplyKindOn (a, b, c) ->
          sprintf "could not apply kind\n\n  %s : %s\n\nwith kind\n\n  %s"
            (Type.Pretty.pretty_print a)
            (Type.Pretty.pretty_print b)
            (Type.Pretty.pretty_print c)
      | EscapedSkolemVariable v ->
          sprintf "escaped skolem variable %s" (Type.Pretty.pretty_print v)
      | TypeVariableNotInScope v ->
          sprintf "type variable not in scope %s" (Type.Pretty.pretty_print v)
      | UnknownVariable n -> sprintf "unknown name %s" n
      | UnknownConstructor c -> sprintf "unknown constructor %s" c
      | InternalError m -> sprintf "internal error: %s" m
  end
end

type t = HintedError of Hints.t list * Message.t [@@deriving eq, show]

let with_message (message : Message.t) : t = HintedError ([], message)

let add_hint (hint : Hints.t) = function
  | HintedError (hints, message) -> HintedError (hint :: hints, message)

let with_hint (hint : Hints.t) : ('a, t) result -> ('a, t) result =
  Result.map_error ~f:(add_hint hint)

module Let = struct
  let ( let* ) : ('a, t) result -> _ = Result.( >>= )

  let ( and* ) : ('a, t) result -> _ = Result.Let_syntax.Let_syntax.both
end

module Pretty = struct
  let pretty_print : t -> string = function
    | HintedError (hints, message) ->
        sprintf "\nan error occurred:\n\n%s\n\n%s\n"
          (Message.Pretty.pretty_print message)
          (List.map ~f:Hints.Pretty.pretty_print hints
          |> String.concat ~sep:"\n\n")
end