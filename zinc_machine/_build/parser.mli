type token =
  | INT of (int)
  | IDENT of (string)
  | FILE_NAME of (string)
  | LPAREN
  | RPAREN
  | BEGIN
  | END
  | LET
  | REC
  | IF
  | ELSE
  | THEN
  | IN
  | COLON
  | COMMA
  | FUN
  | ARROW
  | E
  | TRY
  | WITH
  | PLUS
  | TIMES
  | MINUS
  | EQUAL
  | DIV
  | ENDEXPR
  | REFLET
  | REF
  | EOL
  | RAISE
  | BANG
  | OR
  | AND
  | SGT
  | GT
  | SLT
  | LT
  | NEQUAL
  | NOT
  | PRINTIN
  | AMAKE
  | ARRAYAFFECTATION
  | DOT
  | CONSTRUCTOR of (string)
  | UNDERSCORE
  | SEQ
  | TRUE
  | FALSE
  | OPEN
  | MATCH
  | LISTINSERT
  | RBRACKET
  | LBRACKET
  | INFIX_OP_0 of (string)
  | INFIX_OP_1 of (string)
  | INFIX_OP_2 of (string)
  | INFIX_OP_3 of (string)
  | INFIX_OP_4 of (string)
  | INFIX_OP_REF of (string)
  | PREFIX_OP of (string)
  | TYPE
  | DISJ
  | OF
  | INT_TYPE
  | ARRAY_TYPE
  | UNIT_TYPE
  | BOOL_TYPE
  | POL_TYPE of (string)

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Expr.expr
