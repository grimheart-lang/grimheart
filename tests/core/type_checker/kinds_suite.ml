open Core_kernel
open Grimheart_ast
open Grimheart_core_type_checker

module type TEST_INPUT = sig
  val context : Context.t

  module Environment : Environment.S
end

module Test_utils (I : TEST_INPUT) = struct
  module Kinds = Kinds.Make (I.Environment)

  let infer_kind_test_case annotation value =
    let check () =
      Alcotest.(check bool)
        annotation true
        (Result.is_ok @@ Kinds.infer I.context value)
    in
    Alcotest.test_case annotation `Quick check

  let infer_kind_fail_case annotation value =
    let check () =
      Alcotest.(check bool)
        annotation false
        (Result.is_ok @@ Kinds.infer I.context value)
    in
    Alcotest.test_case annotation `Quick check

  include Type.Primitives
  include Type.Sugar
end

module Test_input : TEST_INPUT = struct
  open Type.Sugar
  open Type.Primitives

  let context : Context.t = [Unsolved "A"; Unsolved "B"]

  module Environment = struct
    include Environment.Make ()

    let () =
      Hashtbl.add_exn environment ~key:"Escape"
        ~data:
          (forall' "a" t_type
          @@ fn (forall "b" @@ fn (var "b") (var "a")) (var "a"));
      Hashtbl.add_exn environment ~key:"Escape'"
        ~data:
          (forall' "a" t_type
          @@ fn (forall' "b" t_type @@ fn (var "b") (var "a")) (var "a"));
      Hashtbl.add_exn environment ~key:"HigherRank"
        ~data:(fn (forall "a" @@ fn (var "a") (var "a")) t_type);
      Hashtbl.add_exn environment ~key:"HigherRank'"
        ~data:(fn (forall' "a" t_type @@ fn (var "a") (var "a")) t_type);
      Hashtbl.add_exn environment ~key:"Identity"
        ~data:(forall' "a" t_type @@ fn (var "a") (var "a"));
      Hashtbl.add_exn environment ~key:"TypeToType" ~data:(fn t_int t_int)
  end
end

let run () =
  let open Alcotest in
  let open Test_utils (Test_input) in
  run ~and_exit:false "Kind Checker Unit Tests"
    [
      ( "infer-higher-rank-kinds"
      , [
          infer_kind_test_case "higher rank kinds with polytypes"
            (Apply (Constructor "HigherRank", Constructor "Identity"))
        ; infer_kind_test_case "higher rank kinds with polytypes, again"
            (Apply (Constructor "HigherRank'", Constructor "Identity"))
        ; infer_kind_test_case "higher rank kinds with monotypes"
            (Apply (Constructor "HigherRank", Constructor "TypeToType"))
        ; infer_kind_test_case "higher rank kinds with monotypes, again"
            (Apply (Constructor "HigherRank'", Constructor "TypeToType"))
        ] )
    ; ( "infer-skolem-escapes"
      , [
          infer_kind_fail_case "skolem escapes are caught"
            (Apply (Constructor "Escape", Constructor "Identity"))
        ; infer_kind_fail_case "skolem escapes are caught, again"
            (Apply (Constructor "Escape'", Constructor "Identity"))
        ] )
    ]
