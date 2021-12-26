{
open Grammar
}

let ascii = ['a'-'z']+
let white = [' ' '\t' '\n']+

rule read =
  parse
  | white { read lexbuf }
  | "let" { LET }
  | "in" { IN }
  | "forall" { FORALL }
  | ascii { IDENT (Lexing.lexeme lexbuf) }
  | "\\" { BACKSLASH }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "()" { UNIT }
  | "=" { EQUAL }
  | ":" { COLON }
  | "." { PERIOD }
  | "->" { ARROW }
  | eof { EOF }
