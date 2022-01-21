open Core_kernel
open Grimheart_ast

type t =
  | FailedUnification of Type.t * Type.t
  | FailedChecking of unit Expr.t * Type.t
  | FailedInfererence of unit Expr.t * Type.t
  | FailedInstantiation of string * Type.t
  | FailedKindChecking of Type.t * Type.t
  | CouldNotUnifyKinds of Type.t * Type.t
  | CouldNotApplyKind of Type.t * Type.t * Type.t
  | InternalKindCheckerError of string
  | IllFormedType of Type.t
  | EscapedSkolemVariable of Type.t
  | VariableNotInScope of Type.t
  | UnknownVariable of string
  | FailedToBreakApart
  | RethrownError of t * t
[@@deriving eq, show]

type 'a result' = ('a, t) Result.t

let rethrow (e : t) : 'a result' -> 'a result' =
  Result.map_error ~f:(fun e' -> RethrownError (e, e'))

module Let = struct
  let ( let* ) : 'a result' -> _ = Result.( >>= )

  let ( and* ) : 'a result' -> _ = Result.Let_syntax.Let_syntax.both
end
