open Core_kernel
open Sulfur_ast

type t =
  | FailedSubtyping of Type.t * Type.t
  | FailedChecking of unit Expr.t * Type.t
  | FailedInfererence of unit Expr.t * Type.t
  | FailedInstantiation of string * Type.t
  | FailedKindChecking of Type.t * Type.t
  | IllFormedType of Type.t
  | UnknownVariable of string
  | FailedToBreakApart
[@@deriving eq, show]

module Let = struct
  let ( let* ) : (_, t) result -> _ = Result.( >>= )

  let ( and* ) : (_, t) result -> _ = Result.Let_syntax.Let_syntax.both
end
