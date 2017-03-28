%{
(* --- préambule: ici du code Caml --- *)

open Expr   (* rappel: dans expr.ml: 
             type expr = Const of int | Add of expr*expr | Mull of expr*expr *)

%}
/* description des lexèmes, ceux-ci sont décrits (par vous) dans lexer.mll */

%token <int> INT       /* le lexème INT a un attribut entier */
%token <string> IDENT
%token LPAREN RPAREN
%token BEGIN END
%token LET REC 
%token IF ELSE THEN
%token IN
%token FUN
%token ARROW
%token E TRY WITH
%token PLUS TIMES MINUS EQUAL
%token ENDEXPR
%token REFLET
%token REF
%token EOL             /* retour à la ligne */
%token RAISE BANG
%token OR AND SGT GT SLT LT NEQUAL  NOT
%token PRINTIN

%nonassoc LETFINAL
%right REFLET
%right ARROW
%right TRY
%right RAISE
%left ELSE IF THEN
%left OR AND
%left SGT GT SLT LT NEQUAL EQUAL
%left PLUS MINUS  /* associativité gauche: a+b+c, c'est (a+b)+c */
%left TIMES  /* associativité gauche: a*b*c, c'est (a*b)*c */
%nonassoc NOT
%left IN
%nonassoc UMINUS  /* un "faux token", correspondant au "-" unaire */
%nonassoc FUN LET  REC
%right REF
%right BANG

%start main             /* "start" signale le point d'entrée: */
                        /* c'est ici main, qui est défini plus bas */
%type <Expr.expr> main     /* on _doit_ donner le type associé au point d'entrée */

%%
    /* --- début des règles de grammaire --- */
                            /* à droite, les valeurs associées */


main:                       /* <- le point d'entrée (cf. + haut, "start") */
    prog ENDEXPR                { $1 }  /* on veut reconnaître un "expr" */
;

identifier:
    | IDENT     {Ident($1)}
unit_type:
    | LPAREN RPAREN { Unit }
int_type:
    | INT               { Const $1 }

types:
    | unit_type { $1 }
    | int_type { $1 }
    | LPAREN prog RPAREN { $2 }
    | identifier              {$1}

basic_types:
    | types { $1 }
    | REF types {Ref($2)}

let_defs:
    | LET identifier fundef EQUAL prog let_defs 
        {In(Let($2, List.fold_left (fun a b -> Fun(b, a)) $5 $3), $6)} 
    | LET REC identifier fundef EQUAL prog let_defs
        {In(LetRec($3, List.fold_left (fun a b -> Fun(b, a)) $6 $4), $7)} 
    | LET identifier fundef EQUAL prog IN prog 
        {In(Let($2, List.fold_left (fun a b -> Fun(b, a)) $5 $3), $7)} 
    | LET REC identifier fundef EQUAL prog IN prog
        {In(LetRec($3, List.fold_left (fun a b -> Fun(b, a)) $6 $4), $8)} 


    | LET identifier fundef EQUAL prog %prec LETFINAL
        {Let($2, List.fold_left (fun a b -> Fun(b, a)) $5 $3)} 
    | LET REC identifier fundef EQUAL prog %prec LETFINAL
        {LetRec($3, List.fold_left (fun a b -> Fun(b, a)) $6 $4)} 

prog:
    | let_defs {$1}
    | FUN identifier ARROW prog {Fun($2, $4)}
    | IF prog THEN prog ELSE prog {IfThenElse($2, $4, $6)}
    | prog PLUS prog          { Add($1,$3) }
    | prog TIMES prog         { Mul($1,$3) }
    | prog MINUS prog         { Minus($1,$3) }
    | prog OR prog         { Or($1,$3) }
    | prog AND prog         { And($1,$3) }
    | prog SLT prog         { Slt($1,$3) }
    | prog LT prog         { Lt($1,$3) }
    | prog SGT prog         { Sgt($1,$3) }
    | prog GT prog         { Gt($1,$3) }
    | MINUS prog %prec UMINUS { Minus(Const 0, $2) }
    | BEGIN prog END        {$2}
    | TRY prog WITH E int_type ARROW prog
    {TryWith($2, $5, $7)}
    | prog REFLET prog {RefLet($1, $3)}
    | RAISE prog {Raise ($2)}
    | BANG prog {Bang($2)}
    | NOT prog {Not($2)}
    | funccall  {$1}
    | prog NEQUAL prog         { Neq($1,$3) }
    | prog EQUAL prog         { Eq($1,$3) }
    | PRINTIN prog          { Printin($2) }
;

funccall:
    | basic_types {$1}
    | funccall basic_types {Call($1, $2)}


fundef:
    |               { [] }
    | fundef unit_type    { $2 :: $1 }
    | fundef identifier {$2 :: $1}
;

