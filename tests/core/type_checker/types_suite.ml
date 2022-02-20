open Core_kernel
open Grimheart_ast
open Grimheart_type_checker

module type TEST_INPUT = sig
  val context : Context.t

  module Environment : Grimheart_environment.S
end

module Test_utils (I : TEST_INPUT) = struct
  module Kinds = Kinds.Make (I.Environment)
  module Types = Types.Make (I.Environment) (Kinds)

  let testable_type_error =
    let open Alcotest in
    result
      (testable Type.pp Type.equal)
      (testable Grimheart_errors.pp Grimheart_errors.equal)

  let testable_context_error =
    let open Alcotest in
    result
      (testable Context.pp Context.equal)
      (testable Grimheart_errors.pp Grimheart_errors.equal)

  let infer_type_check_test_case annotation expected value =
    let check () =
      Alcotest.check testable_type_error annotation (Ok expected)
        (Types.infer_type_with I.context value)
    in
    Alcotest.test_case annotation `Quick check

  let infer_type_check_fail_case annotation value =
    let check () =
      Alcotest.(check bool)
        annotation false
        (Result.is_ok @@ Types.infer_type_with I.context value)
    in
    Alcotest.test_case annotation `Quick check

  let t1_t2_test_case fn annotation t1 t2 =
    let check () =
      Alcotest.(check bool) annotation true (Result.is_ok @@ fn I.context t1 t2)
    in
    Alcotest.test_case annotation `Quick check

  let t1_t2_fail_case fn annotation t1 t2 =
    let check () =
      Alcotest.(check bool) annotation false (Result.is_ok @@ fn I.context t1 t2)
    in
    Alcotest.test_case annotation `Quick check

  let subsumes_test_case = t1_t2_test_case Types.subsumes

  let subsumes_fail_case = t1_t2_fail_case Types.subsumes

  let unify_test_case = t1_t2_test_case Types.unify

  let unify_fail_case = t1_t2_fail_case Types.unify

  let check_fail_case = t1_t2_fail_case Types.check

  include Type.Primitives
  include Type.Sugar
end

module Test_input : TEST_INPUT = struct
  open Type.Sugar

  let context : Context.t = [Unsolved "A"; Unsolved "B"]

  module Environment = struct
    include Grimheart_environment.Make ()

    let () =
      let open Names.Mutable in
      set "identity" (forall "a" @@ fn (var "a") (var "a"));
      set "escape"
        (forall "a" @@ fn (forall "b" @@ fn (var "b") (var "a")) (var "a"))
  end
end

let run () =
  let open Alcotest in
  let open Test_utils (Test_input) in
  run ~and_exit:false "Type Checker Unit Tests"
    [
      ( "infer-literal-scalar"
      , [
          infer_type_check_test_case "infer char literal" t_char
            (Expr.Literal (Char 'a'))
        ; infer_type_check_test_case "infer string literal" t_string
            (Expr.Literal (String "a"))
        ; infer_type_check_test_case "infer int literal" t_int
            (Expr.Literal (Int 0))
        ; infer_type_check_test_case "infer float literal" t_float
            (Expr.Literal (Float 0.))
        ] )
    ; ( "infer-literal-array-scalar"
      , let make (t, l) =
          match t with
          | Type.Constructor t ->
              infer_type_check_test_case
                (Printf.sprintf "infer array %s literal" (String.lowercase t))
                (ap t_array (Type.Constructor t))
                (Expr.Literal (Literal.Array [Expr.Literal l; Expr.Literal l]))
          | _ -> failwith "not a constructor"
        in
        List.map ~f:make
          [
            (t_char, Literal.Char 'a')
          ; (t_string, Literal.String "a")
          ; (t_int, Literal.Int 0)
          ; (t_float, Literal.Float 0.)
          ] )
    ; ( "infer-literal-array-empty"
      , [
          infer_type_check_test_case "infer empty array literal"
            (forall "a" @@ ap t_array (var "a"))
            (Expr.Literal (Literal.Array []))
        ] )
    ; ( "subsumes-monotype"
      , [
          subsumes_test_case "monotype function subsumes with monotype function"
            (fn t_int t_int) (fn t_int t_int)
        ; subsumes_fail_case "monotype does not subsume polytype" t_int
            (forall "a" @@ var "a")
        ; subsumes_fail_case
            "monotype function does not subsume with polytype function"
            (fn t_int t_int)
            (forall "a" @@ fn (var "a") (var "a"))
        ] )
    ; ( "subsumes-polytype"
      , [
          subsumes_test_case "polytype subsumes with polytype"
            (forall "a" @@ var "a")
            (forall "b" @@ var "b")
        ; subsumes_test_case "polytype subsumes with monotype"
            (forall "a" @@ var "a")
            t_int
        ; subsumes_test_case "polytype function subsumes with polytype function"
            (forall "a" @@ forall "b" @@ fn (var "a") (var "b"))
            (forall "c" @@ forall "d" @@ fn (var "c") (var "d"))
        ; subsumes_test_case "polytype function subsumes with monotype function"
            (forall "a" @@ fn (var "a") (var "a"))
            (fn t_int t_int)
        ; subsumes_test_case
            "polytype subsumes with partially polytyped function"
            (forall "a" @@ forall "b" @@ fn (var "a") (var "b"))
            (forall "c" @@ fn (var "c") t_int)
        ] )
    ; ( "unify-polytype"
      , [
          unify_test_case "polytype unifies with polytype"
            (forall "a" @@ var "a")
            (forall "b" @@ var "b")
        ; unify_fail_case "polytype does not unify with monotype"
            (forall "a" @@ var "a")
            t_int
        ; unify_fail_case "monotypw does not unify with polytype" t_int
            (forall "a" @@ var "a")
        ] )
    ; ( "unify-unsolved"
      , [
          unify_test_case "reflexive unsolved types unify" (uns "A") (uns "A")
        ; unify_test_case "well-formed unsolved types unify" (uns "A") (uns "B")
        ; unify_test_case "well-formed unsolved types unify flipped" (uns "B")
            (uns "A")
        ] )
    ; ( "unify-application"
      , [
          unify_test_case "reflexive function application unifies"
            (ap (fn t_int t_int) t_int)
            (ap (fn t_int t_int) t_int)
        ] )
    ; ( "infer-skolem-escapes"
      , [
          infer_type_check_fail_case "skolem escapes are caught"
            (Apply (Variable "escape", Variable "identity"))
        ] )
    ; ( "infer-polymorphic-lambda"
      , [
          infer_type_check_test_case "lambdas are generalized"
            (forall "a" @@ fn (var "a") (var "a"))
            (Lambda ("a", Variable "a"))
        ; infer_type_check_test_case "lambda application is inferred" t_int
            (Apply (Lambda ("a", Variable "a"), Literal (Int 0)))
        ; infer_type_check_fail_case "infinite types are caught"
            (Lambda ("a", Apply (Variable "a", Variable "a")))
        ; infer_type_check_test_case "infer functions as arguments"
            (forall "a" @@ fn (fn t_int (var "a")) (var "a"))
            (Lambda ("f", Apply (Variable "f", Literal (Int 0))))
        ] )
    ; ( "infer-annotation"
      , [
          infer_type_check_test_case "annotations are checked" t_int
            (Annotate (Literal (Int 0), t_int))
        ; infer_type_check_fail_case "annotations are checked"
            (Annotate (Literal (Int 0), t_float))
        ] )
    ; ( "infer-let"
      , [
          infer_type_check_test_case "let bounds variable" t_string
            (Let ("a", None, Literal (String "a"), Variable "a"))
        ; infer_type_check_test_case "let type annotations are checked" t_string
            (Let ("a", Some t_string, Literal (String "a"), Variable "a"))
        ; infer_type_check_fail_case "let inference does not generalize"
            (Let
               ( "id'"
               , None
               , Lambda ("a", Variable "a")
               , Let
                   ( "_1"
                   , None
                   , Apply (Variable "id'", Literal (Int 0))
                   , Let
                       ( "_2"
                       , None
                       , Apply (Variable "id'", Literal (Float 0.))
                       , Literal (Char '0') ) ) ))
        ; infer_type_check_test_case "let inference with annotation" t_char
            (Let
               ( "id'"
               , Some (forall "a" @@ fn (var "a") (var "a"))
               , Lambda ("a", Variable "a")
               , Let
                   ( "_1"
                   , None
                   , Apply (Variable "id'", Literal (Int 0))
                   , Let
                       ( "_2"
                       , None
                       , Apply (Variable "id'", Literal (Float 0.))
                       , Literal (Char '0') ) ) ))
        ] )
    ]
