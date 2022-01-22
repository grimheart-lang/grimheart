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
