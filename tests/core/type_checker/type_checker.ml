open Sulfur_ast
open Sulfur_type_checker

module Test_utils = struct
  let testable_type_error =
    let open Alcotest in
    result
      (testable Type.pp Type.equal)
      (testable Sulfur_errors.pp Sulfur_errors.equal)

  let infer_type_check_test_case annotation speed expected value =
    let check () =
      Alcotest.check testable_type_error annotation (Ok expected)
        (Types.infer_type value)
    in
    Alcotest.test_case annotation speed check
end

let () =
  let open Alcotest in
  let open Test_utils in
  let open Type.Primitives in
  run "Core"
    [
      ( "infer-literal-scalar"
      , [
          infer_type_check_test_case "infer char literal" `Quick t_char
            (Expr.Literal (Char 'a'))
        ; infer_type_check_test_case "infer string literal" `Quick t_string
            (Expr.Literal (String "a"))
        ; infer_type_check_test_case "infer int literal" `Quick t_int
            (Expr.Literal (Int 0))
        ; infer_type_check_test_case "infer float literal" `Quick t_float
            (Expr.Literal (Float 0.))
        ] )
    ; ( "infer-literal-array-scalar"
      , let make (t, l) =
          match t with
          | Type.Constructor t ->
              infer_type_check_test_case
                (Printf.sprintf "infer array %s literal"
                   (String.lowercase_ascii t))
                `Quick
                (* todo: this annotation gets erased in the future *)
                (Apply (t_array, Annotate (Type.Constructor t, t_type)))
                (Expr.Literal (Literal.Array [Expr.Literal l; Expr.Literal l]))
          | _ -> failwith "not a constructor"
        in
        List.map make
          [
            (t_char, Char 'a')
          ; (t_string, String "a")
          ; (t_int, Int 0)
          ; (t_float, Float 0.)
          ] )
    ; ( "infer-literal-array-empty"
      , [
          infer_type_check_test_case "infer empty array literal" `Quick
            (* todo: this annotation gets erased in the future. make sure to
               shift it inside the forall annotation instead. *)
            (Forall ("a", None, Apply (t_array, Annotate (Variable "a", t_type))))
            (Expr.Literal (Literal.Array []))
        ] )
    ]
