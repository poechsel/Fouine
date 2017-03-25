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
%token PLUS TIMES MINUS EQUAL
%token ENDEXPR
%token EOL             /* retour à la ligne */

%left PLUS MINUS  /* associativité gauche: a+b+c, c'est (a+b)+c */
%left TIMES  /* associativité gauche: a*b*c, c'est (a*b)*c */
%left ELSE
%right ARROW
%left IN
%nonassoc UMINUS  /* un "faux token", correspondant au "-" unaire */
%nonassoc FUN LET IF THEN REC

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
unit_type:
    | LPAREN RPAREN { Unit }

basic_types:
    | unit_type { $1 }
    | INT               { Const $1 }
    | LPAREN prog RPAREN { $2 }
    | identifier              {$1}


prog:
    | LET REC identifier fundef EQUAL prog IN prog 
        {In(Aff($3, List.fold_left (fun a b -> FunRec(b, a)) $6 $4), $8)} 
    | LET identifier fundef EQUAL prog IN prog 
        {In(Aff($2, List.fold_left (fun a b -> Fun(b, a)) $5 $3), $7)} 
    | FUN identifier ARROW prog {Fun($2, $4)}
    | IF prog THEN prog ELSE prog {IfThenElse($2, $4, $6)}
    | prog PLUS prog          { Add($1,$3) }
    | prog TIMES prog         { Mul($1,$3) }
    | prog MINUS prog         { Minus($1,$3) }
    | MINUS prog %prec UMINUS { Minus(Const 0, $2) }
    | BEGIN prog END        {$2}
    | funccall  {$1}
;

funccall:
    | basic_types {$1}
    | funccall basic_types {Call($1, $2)}


fundef:
    |               { [] }
    | fundef unit_type    { $2 :: $1 }
    | fundef identifier {$2 :: $1}
;

