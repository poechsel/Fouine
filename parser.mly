%{
(* --- préambule: ici du code Caml --- *)

open Expr   (* rappel: dans expr.ml: 
             type expr = Const of int | Add of expr*expr | Mull of expr*expr *)

%}
/* description des lexèmes, ceux-ci sont décrits (par vous) dans lexer.mll */

%token <int> INT       /* le lexème INT a un attribut entier */
%token <string> IDENT
%token PLUS TIMES MINUS EQUAL
%token ARROW
%token LPAREN RPAREN
%token BEGIN END
%token LET IN REC 
%token IF ELSE THEN
%token FUN
%token ENDEXPR
%token EOL             /* retour à la ligne */

%left PLUS MINUS  /* associativité gauche: a+b+c, c'est (a+b)+c */
%left TIMES  /* associativité gauche: a*b*c, c'est (a*b)*c */
%nonassoc UMINUS  /* un "faux token", correspondant au "-" unaire */

%start main             /* "start" signale le point d'entrée: */
                        /* c'est ici main, qui est défini plus bas */
%type <Expr.expr> main     /* on _doit_ donner le type associé au point d'entrée */

%%
    /* --- début des règles de grammaire --- */
                            /* à droite, les valeurs associées */


main:                       /* <- le point d'entrée (cf. + haut, "start") */
    prog EOL                { $1 }  /* on veut reconnaître un "expr" */
;

identifier:
    | IDENT     {Ident($1)}

basic_types:
    | LPAREN RPAREN { Unit }
    | INT               { Const $1 }
    | LPAREN prog RPAREN { $2 }
    | identifier              {$1}


prog:
    | basic_types               { $1 }
    | prog PLUS prog          { Add($1,$3) }
    | prog TIMES prog         { Mul($1,$3) }
    | prog MINUS prog         { Minus($1,$3) }
    | MINUS prog %prec UMINUS { Minus(Const 0, $2) }
    | BEGIN prog END        {$2}
    | IF prog THEN prog ELSE prog {IfThenElse($2, $4, $6)}
    | FUN identifier ARROW prog {Fun($2, $4)}
    | LET identifier fundef     {Aff($2, $3)}
    | LET REC identifier funrecdef     {Aff($3, $4)}
    | identifier elements {Call($1, $2)}
;

elements:
    | basic_types   {[$1]}
    | basic_types elements {$1::$2}

fundef:
    | EQUAL prog  {$2}
    | identifier fundef      {Fun($1, $2)}
;
funrecdef:
    | EQUAL prog  {$2}
    | identifier funrecdef      {FunRec($1, $2)}
;
