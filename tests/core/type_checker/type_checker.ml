open Core_kernel
open Grimheart_ast
open Grimheart_core_type_checker

module Test_utils = struct
  let testable_type_error =
    let open Alcotest in
    result
      (testable Type.pp Type.equal)
      (testable Grimheart_core_errors.pp Grimheart_core_errors.equal)

  let testable_context_error =
    let open Alcotest in
    result
      (testable Context.pp Context.equal)
      (testable Grimheart_core_errors.pp Grimheart_core_errors.equal)

  let infer_type_check_test_case annotation expected value =
    let check () =
      Alcotest.check testable_type_error annotation (Ok expected)
        (Types.infer_type value)
    in
    Alcotest.test_case annotation `Quick check

  let subsumes_test_case annotation t1 t2 =
    let check () =
      Alcotest.(check bool)
        annotation true
        (Result.is_ok @@ Types.subsumes [] t1 t2)
    in
    Alcotest.test_case annotation `Quick check

  let subsumes_fail_case annotation t1 t2 =
    let check () =
      Alcotest.(check bool)
        annotation false
        (Result.is_ok @@ Types.subsumes [] t1 t2)
    in
    Alcotest.test_case annotation `Quick check

  let unify_test_case annotation t1 t2 =
    let check () =
      Alcotest.(check bool)
        annotation true
        (Result.is_ok @@ Types.unify [Unsolved "A"; Unsolved "B"] t1 t2)
    in
    Alcotest.test_case annotation `Quick check

  let unify_fail_case annotation t1 t2 =
    let check () =
      Alcotest.(check bool)
        annotation false
        (Result.is_ok @@ Types.unify [] t1 t2)
    in
    Alcotest.test_case annotation `Quick check

  module Sweeter = struct
    include Grimheart_ast.Type.Primitives
    include Grimheart_ast.Type.Sugar

    let forall a t = Type.Forall (a, None, t)

    let forall' a k t = Type.Forall (a, Some k, t)

    let var a = Type.Variable a

    let uns a = Type.Unsolved a
  end
end

let () =
  let open Alcotest in
  let open Test_utils in
  let open Test_utils.Sweeter in
  run "Core"
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
    ]
