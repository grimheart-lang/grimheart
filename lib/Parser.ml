open Syntax

let parse (source : string) : expr_t =
  let lexbuf = Lexing.from_string source in
  let ast = Grammar.program Lexer.read lexbuf in
  ast
