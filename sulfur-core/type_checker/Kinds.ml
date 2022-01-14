open Sulfur_ast

let check_kind (gamma : Context.t) (_T : Type.t) (_K : Type.t) :
    (Context.t, Sulfur_errors.t) result =
  Log.error "Kind checker hasn't been implemented yet!";
  Ok gamma
