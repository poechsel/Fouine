{
  open Parser;;        (* le type "token" est défini dans parser.mli *)
(* ce n'est pas à vous d'écrire ce fichier, il est engendré automatiquement *)
exception Eof;;
let incr_linenum lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- {pos with
        Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
        Lexing.pos_bol = pos.Lexing.pos_cnum;
    }
}


let symbol = ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~']

rule token = parse    (* la "fonction" aussi s'appelle token .. *)
  | [' ' '\t']     { token lexbuf }    (* on saute les blancs et les tabulations *)
  | '\n' {incr_linenum lexbuf; token lexbuf}
 	     	   	           (* token: appel récursif *)
                                   (* lexbuf: argument implicite
                                      associé au tampon où sont
                                      lus les caractères *)
  | '\n'            { EOL }
  | "int"           { INT_TYPE }
  | "array"         { ARRAY_TYPE }
  | "bool"          { BOOL_TYPE } 
  | "unit"          { UNIT_TYPE }
  | "open"          { OPEN } 
  | "type"          { TYPE }
  | "|"             { DISJ }
  | "of"            { OF }
  | ","             { COMMA }
 (* | "prInt"         { PRINTIN }*)
  |"ref"            { REF }
 (* | "aMake"         { AMAKE } *)
  | '+'             { PLUS }
  | '/'             { DIV }
  | '*'             { TIMES }
  | ":="            { REFLET }
  | '-'             { MINUS }
  | '='             { EQUAL }
  | ";"             { SEQ }
  | '('             { LPAREN }
  | "_"             { UNDERSCORE }
  | ')'             { RPAREN }
  | "->"            { ARROW }
  | "match"         { MATCH }
  | "let"           { LET }
  | "in"            { IN }
  | "begin"         { BEGIN }
  | "true"          { TRUE }
  | "false"         { FALSE }
  | "end"           { END }
  | "rec"           { REC }
  | "if"            { IF }
  | "then"          { THEN }
  | "else"          { ELSE }
  | "fun"           { FUN }
  | (eof|";;")      { ENDEXPR }
  | "try"           { TRY }
  | "E"             { E }
  | "with"          { WITH }
  | "!"             { BANG }
  | "raise"         { RAISE }
  | "<="            { LT }
  | ">="            { GT }
  | "<"             { SLT }
  | ">"             { SGT }
  | "<>"            { NEQUAL }
  | "not"           { NOT }
  | "&&"            { AND }
  | "::"            { LISTINSERT }
  | "]"             { RBRACKET }
  | "["             { LBRACKET }
  | "||"            { OR }
  | "<-"            { ARRAYAFFECTATION }
  | "."             { DOT }


  | "!"symbol* as s	{PREFIX_OP s}
  | ['~' '?'] symbol+ as s	{PREFIX_OP s}

  | ['=' '<' '>' '|' '&' '$'] symbol* as s {INFIX_OP_0 s}
  | ['@' '^'] symbol* as s {INFIX_OP_1 s}
  | ['+' '-'] symbol* as s {INFIX_OP_2 s}
  | "**" symbol* as s {INFIX_OP_4 s}
  | ['*' '/' '%'] symbol* as s {INFIX_OP_3 s}
  | ":="    as s {INFIX_OP_REF s}


  | '"'('/'|['a'-'z']['0'-'9''a'-'z''A'-'Z''_''.']*)*'"' as s {FILE_NAME (String.sub s 1 (String.length s - 2))}
  | ['a'-'z']['0'-'9''a'-'z''A'-'Z''_']*'\''* as s {IDENT (s)}
  | "'"['0'-'9''a'-'z''A'-'Z''_']*'\''* as s {POL_TYPE (s)}
  | ['A'-'Z']['0'-'9''a'-'z''A'-'Z''_']*'\''* as s {CONSTRUCTOR (s)}
  | ['0'-'9']+ as s { INT (int_of_string s) }
  | eof             { EOL} 
