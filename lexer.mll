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



rule token = parse    (* la "fonction" aussi s'appelle token .. *)
  | [' ' '\t']     { token lexbuf }    (* on saute les blancs et les tabulations *)
  | "open "['a'-'z']['0'-'9''a'-'z''A'-'Z''_''.']* as s {FILE_NAME (s)}
  | '\n' {incr_linenum lexbuf; token lexbuf}
 	     	   	           (* token: appel récursif *)
                                   (* lexbuf: argument implicite
                                      associé au tampon où sont
                                      lus les caractères *)
  | '\n'            { EOL }
  | "prInt"         { PRINTIN }
  | '+'             { PLUS }
  | '/'             { DIV }
  | '*'             { TIMES }
  | '-'             { MINUS }
  | '='             { EQUAL }
  | ";"             { SEQ }
  | '('             { LPAREN }
  | "_"             { UNDERSCORE }
  | ')'             { RPAREN }
  | "->"            { ARROW }
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
  | ";;"            { ENDEXPR }
  | "try"           { TRY }
  | "E"             { E }
  | "with"          { WITH }
  | ":="            { REFLET }
  | "!"             { BANG }
  | "raise"         { RAISE }
  | "ref"           { REF }
  | "<="            { LT }
  | ">="            { GT }
  | "<"             { SLT }
  | ">"             { SGT }
  | "<>"            { NEQUAL }
  | "not"           { NOT }
  | "&&"            { AND }
  | "||"            { OR }
  | "<-"            { ARRAYAFFECTATION }
  | "."             { DOT }
  | "aMake"         { AMAKE }
  | ['a'-'z']['0'-'9''a'-'z''A'-'Z''_']*'\''* as s {IDENT (s)}
  | ['0'-'9']+ as s { INT (int_of_string s) }
  | eof             { EOL} 
