%token LPAREN RPAREN UNIT
%token EQUAL COLON BACKSLASH PERIOD ARROW

%token LET IN FORALL
%token <string> IDENT

%token EOF

%start <Syntax.expr_t> program

%%

program:
  | e = expr; EOF { e }
  ;

expr:
  | e = expr1 { e }
  | e = expr1; COLON; t = type_ { Syntax.EAnnotation (e, t) }
  ;

expr1:
  | e = expr2 { e }
  | f = expr1; x = expr2 { Syntax.EApplication (f, x) }
  ;

expr2:
  | e = expr3 { e }
  | BACKSLASH; i = IDENT; PERIOD; e = expr { Syntax.EAbstraction (i, e) }
  ;

expr3:
  | e = exprAtom { e }
  | LET; i = IDENT; EQUAL; x = expr; IN; e = expr { Syntax.ELet (i, None, x, e) }
  | LET; i = IDENT; COLON; t = type_; EQUAL; x = expr; IN; e = expr { Syntax.ELet (i, Some t, x, e) }
  ;

exprAtom:
  | UNIT { Syntax.EUnit }
  | i = IDENT { Syntax.EVariable i }
  | LPAREN; e = expr; RPAREN { e }
  ;

type_:
  | t = type1 { t }
  | FORALL; i = IDENT; PERIOD; t = type_ { Syntax.PForall (i, t) }
  ;

type1:
  | t = typeAtom { t }
  | a = typeAtom; ARROW; b = type_ { Syntax.PFunction (a, b) }
  ;

typeAtom:
  | UNIT { Syntax.PUnit }
  | i = IDENT; { Syntax.PVariable i }
  | LPAREN; t = type_; RPAREN { t }
