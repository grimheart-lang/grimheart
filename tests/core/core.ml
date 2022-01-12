open Sulfur_core

module Test_utils = struct
  let pp_type_error formatter = function
    | Ok t -> Type.pp formatter t
    | Error e -> Infer.Error.pp formatter e

  let testable_type_error =
    Alcotest.testable pp_type_error
      (Result.equal ~ok:Type.equal ~error:Infer.Error.equal)

  let infer_type_check_test_case annotation speed expected value =
    let check () =
      Alcotest.check testable_type_error annotation (Ok expected)
        (Infer.infer_type value)
    in
    Alcotest.test_case annotation speed check
end

let () =
  let open Alcotest in
  let open Test_utils in
  let open Type.Primitives in
  run "Core"
    [
      ( "infer-literal"
      , [
          infer_type_check_test_case "infer char literal" `Quick t_char
            (Expr.Literal (Char 'a'))
        ; infer_type_check_test_case "infer string literal" `Quick t_string
            (Expr.Literal (String "a"))
        ; infer_type_check_test_case "infer int literal" `Quick t_int
            (Expr.Literal (Int 0))
        ; infer_type_check_test_case "infer float literal" `Quick t_float
            (Expr.Literal (Float 0.))
        ; infer_type_check_test_case "infer array literal" `Quick
            (Type.Sugar.ap t_array t_int)
            (Expr.Literal (Literal.Array [Expr.Literal (Int 0)]))
        ; infer_type_check_test_case "infer object literal" `Quick
            (Type.Sugar.ap (Type.Constructor "Object") t_int)
            (Expr.Literal (Literal.Object [("a", Expr.Literal (Int 0))]))
        ] )
    ]
