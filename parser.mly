%{
(* --- préambule: ici du code Caml --- *)

open Expr   (* rappel: dans expr.ml: 
             type expr = Const of int | Add of expr*expr | Mull of expr*expr *)

%}
/* description des lexèmes, ceux-ci sont décrits (par vous) dans lexer.mll */

%token <int> INT       /* le lexème INT a un attribut entier */
%token <string> IDENT
%token <string> FILE_NAME
%token LPAREN RPAREN
%token BEGIN END
%token LET REC 
%token IF ELSE THEN
%token IN
%token FUN
%token ARROW
%token E TRY WITH
%token PLUS TIMES MINUS EQUAL DIV
%token ENDEXPR
%token REFLET
%token REF
%token EOL             /* retour à la ligne */
%token RAISE BANG
%token OR AND SGT GT SLT LT NEQUAL  NOT
%token PRINTIN
%token AMAKE
%token ARRAYAFFECTATION
%token DOT
%token UNDERSCORE
%token SEQ 
%token TRUE
%token FALSE
%token OPEN
%token GUILLEMET

%nonassoc LETFINAL
%left IN
%left SEQ
%right REFLET
%right ARROW
%right TRY
%right ARRAYAFFECTATION
%right RAISE
%left ELSE IF THEN
%left OR AND
%left SGT GT SLT LT NEQUAL EQUAL
%left PLUS MINUS  /* associativité gauche: a+b+c, c'est (a+b)+c */
%left TIMES DIV  /* associativité gauche: a*b*c, c'est (a*b)*c */
%nonassoc NOT
%nonassoc UMINUS  /* un "faux token", correspondant au "-" unaire */
%nonassoc FUN LET  REC
%nonassoc PRINTIN
%nonassoc AMAKE
%right REF
%right BANG

%start main             /* "start" signale le point d'entrée: */
                        /* c'est ici main, qui est défini plus bas */
%type <Expr.expr> main     /* on _doit_ donner le type associé au point d'entrée */

%%
    /* --- début des règles de grammaire --- */
                            /* à droite, les valeurs associées */


main:                       /* <- le point d'entrée (cf. + haut, "start") */
    main_body {$1}
;

main_body:
    | EOL {Eol}
    | ENDEXPR {Eol}
    | OPEN FILE_NAME ENDEXPR {Open($2, Parsing.rhs_start_pos 1)}
    | prog ENDEXPR                { $1 }  /* on veut reconnaître un "expr" */


identifier:
    | IDENT     {Ident($1, Parsing.rhs_start_pos 1)}
    | underscore_type { $1 }
unit_type:
    | LPAREN RPAREN { Unit }
underscore_type:
    | UNDERSCORE {Underscore}
int_type:
    | INT               { Const $1 }
array_type :
    | identifier DOT LPAREN prog RPAREN {ArrayItem($1, $4, Parsing.rhs_start_pos 1)}

identifier_list:
    | identifier identifier_list {$1 :: $2}
    | identifier {[$1]}

types:
    | unit_type { $1 }
    | int_type { $1 }
    | LPAREN prog RPAREN { $2 }
    | identifier              {$1}
    | array_type            {$1}


basic_types:
    | types { $1 }
    | REF types {Ref($2, Parsing.rhs_start_pos 2)}
    | TRUE {Bool true}
    | FALSE {Bool false}

main_scope_decl:
    | OPEN FILE_NAME {[Open($2, Parsing.rhs_start_pos 1)]}
    | OPEN FILE_NAME main_scope_decl
    {(Open($2, Parsing.rhs_start_pos 1))::$3}
    | LET identifier fundef EQUAL prog %prec LETFINAL
        {[Let($2, List.fold_left (fun a (b, c) -> Fun(b, a, c)) $5 $3, Parsing.rhs_start_pos 1)]} 
    | LET REC identifier fundef EQUAL prog %prec LETFINAL
        {[LetRec($3, List.fold_left (fun a (b, c) -> Fun(b, a, c)) $6 $4, Parsing.rhs_start_pos 1)]} 
    | LET identifier fundef EQUAL prog main_scope_decl 
        {(Let($2, List.fold_left (fun a (b, c) -> Fun(b, a, c)) $5 $3, Parsing.rhs_start_pos 1)) :: $6} 
    | LET REC identifier fundef EQUAL prog main_scope_decl
        {(LetRec($3, List.fold_left (fun a (b, c) -> Fun(b, a, c)) $6 $4, Parsing.rhs_start_pos 1)) :: $7} 
    

let_defs:
    | LET identifier fundef EQUAL prog %prec LETFINAL
        {Let($2, List.fold_left (fun a (b, c) -> Fun(b, a, c)) $5 $3, Parsing.rhs_start_pos 1)} 
    | LET REC identifier fundef EQUAL prog %prec LETFINAL
        {LetRec($3, List.fold_left (fun a (b, c) -> Fun(b, a, c)) $6 $4, Parsing.rhs_start_pos 1)} 
    | LET identifier fundef EQUAL prog IN prog 
        {In(Let($2, List.fold_left (fun a (b, c) -> Fun(b, a, c)) $5 $3, Parsing.rhs_start_pos 1), $7, Parsing.rhs_start_pos 6)} 
    | LET REC identifier fundef EQUAL prog IN prog
        {In(LetRec($3, List.fold_left (fun a (b, c) -> Fun(b, a, c)) $6 $4, Parsing.rhs_start_pos 1), $8, Parsing.rhs_start_pos 7)} 



prog:
    | PRINTIN prog          { Printin($2, Parsing.rhs_start_pos 1) }
    | AMAKE prog            { ArrayMake ($2, Parsing.rhs_start_pos 1) }
    | let_defs {$1}
    | prog  SEQ prog         {Seq($1, $3, Parsing.rhs_start_pos 2)}
    | FUN identifier_list ARROW prog 
    {let d = Parsing.rhs_start_pos 1 
    in let l = List.rev $2
    in List.fold_left (fun a b -> Fun(b, a, d)) (Fun(List.hd l, $4, d)) (List.tl l)}
    | IF prog THEN prog ELSE prog {IfThenElse($2, $4, $6 ,Parsing.rhs_start_pos 1)}
    | prog PLUS prog          { BinOp(addOp, $1,$3, Parsing.rhs_start_pos 2) }
    | prog TIMES prog         { BinOp(multOp, $1,$3, Parsing.rhs_start_pos 2) }
    | prog DIV prog         { BinOp(divOp, $1,$3, Parsing.rhs_start_pos 2) }
    | prog MINUS prog         { BinOp(minusOp, $1,$3, Parsing.rhs_start_pos 2) }
    | prog OR prog         { BinOp(orOp, $1,$3, Parsing.rhs_start_pos 2) }
    | prog AND prog         { BinOp(andOp, $1,$3, Parsing.rhs_start_pos 2) }
    | prog SLT prog         { BinOp(sltOp, $1,$3, Parsing.rhs_start_pos 2) }
    | prog LT prog         { BinOp(ltOp, $1,$3, Parsing.rhs_start_pos 2) }
    | prog SGT prog         { BinOp(sgtOp, $1,$3, Parsing.rhs_start_pos 2) }
    | prog GT prog         { BinOp(gtOp, $1,$3, Parsing.rhs_start_pos 2) }
    | MINUS prog %prec UMINUS { BinOp(minusOp, Const 0, $2, Parsing.rhs_start_pos 1) }
    | BEGIN prog END        {$2}
    | TRY prog WITH E identifier ARROW prog
    {TryWith($2, $5, $7, Parsing.rhs_start_pos 1)}
    | TRY prog WITH E int_type ARROW prog
    {TryWith($2, $5, $7, Parsing.rhs_start_pos 1)}
    
    | prog REFLET prog {BinOp(refSet, $1, $3, Parsing.rhs_start_pos 2)}
    | RAISE prog {Raise ($2, Parsing.rhs_start_pos 1)}
    | BANG prog {Bang($2, Parsing.rhs_start_pos 1)}
    | NOT prog {Not($2, Parsing.rhs_start_pos 1)}
    | funccall  {$1}
    | prog NEQUAL prog         { BinOp(neqOp, $1,$3, Parsing.rhs_start_pos 2) }
    | prog EQUAL prog         { BinOp(eqOp, $1,$3, Parsing.rhs_start_pos 2) }
    | array_type ARRAYAFFECTATION prog 
        {match ($1) with
        | ArrayItem (x, y, _) -> ArraySet(x, y, $3, Parsing.rhs_start_pos 2)
        | _ -> failwith "error"}


;

funccall:
    | basic_types {$1}
    | funccall basic_types {Call($1, $2, Parsing.rhs_start_pos 2)}


fundef:
    |               { [] }
    | fundef unit_type    { ($2, Parsing.rhs_start_pos 2) :: $1 }
    | fundef identifier {($2, Parsing.rhs_start_pos 2) :: $1}
;

