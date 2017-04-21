%{
(* --- préambule: ici du code Caml --- *)

open Expr   (* rappel: dans expr.ml: 
             type expr = Const of int | Add of expr*expr | Mull of expr*expr *)

let rec transfo_poly_types tbl t =
    let aux = transfo_poly_types tbl in
    match t with
    | Var_type x -> (x := aux !x ; t)
    | Ref_type x -> Ref_type (aux x)
    | Fun_type (a, b) -> Fun_type (aux a, aux b)
    | Tuple_type l -> Tuple_type (List.map aux l)
    | Params_type l -> Params_type (List.map aux l)
    | Called_type (n, t) -> Called_type (n, aux t)
    | Arg_type x -> Arg_type (aux x)
    | Polymorphic_type s ->
            if Hashtbl.mem tbl s then
                Var_type (Hashtbl.find tbl s)
            else 
                let u = get_new_pol_type ()
                in (Hashtbl.add tbl s u; Var_type u)
    | Constructor_type (n, a, b) ->
            Constructor_type (n, aux a, aux b)
    | Constructor_type_noarg(n, a) ->
            Constructor_type_noarg (n, aux a)
    | _ -> t
let transfo_typedecl typedecl = 
    match typedecl with
    | TypeDecl (name, lst, er) ->
            let tbl = Hashtbl.create 0
            in TypeDecl(transfo_poly_types tbl name, List.map (transfo_poly_types tbl) lst, er)
    | _ -> typedecl

%}
/* description des lexèmes, ceux-ci sont décrits (par vous) dans lexer.mll */

%token <int> INT       /* le lexème INT a un attribut entier */
%token <string> IDENT
%token COMMENT
%token <string> FILE_NAME
%token LPAREN RPAREN
%token BEGIN END
%token LET REC 
%token IF ELSE THEN
%token IN
%token COMMA
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
%token <string> CONSTRUCTOR
%token UNDERSCORE
%token SEQ 
%token TRUE
%token FALSE
%token OPEN
%token MATCH 

%token TYPE DISJ OF
%token INT_TYPE ARRAY_TYPE UNIT_TYPE BOOL_TYPE 
%token <string> POL_TYPE

/* precedence order of elements. Unfortunately, their wasn't enough time to fully test if these precedences are correct */
%nonassoc IFFINAL
%nonassoc IDENT
%left IN
%left SEQ
%left LET
%nonassoc below_WITH
%nonassoc WITH
%nonassoc THEN
%nonassoc ELSE
%left DISJ
%nonassoc below_COMMA
%left COMMA
%right REFLET
%right ARROW
%right TRY
%right ARRAYAFFECTATION
%right RAISE
%left IF 
%left OR AND
%left SGT GT SLT LT NEQUAL EQUAL
%left PLUS MINUS
%left TIMES DIV  
%nonassoc NOT
%nonassoc UMINUS  
%nonassoc FUN  REC
%nonassoc PRINTIN
%nonassoc AMAKE
%nonassoc DOT
%right REF
%right BANG
%nonassoc LPAREN RPAREN
%left CONSTRUCTOR

%start main             
                       
%type <Expr.expr> main

%%

main:                     
    main_body {$1}
;

main_body:
    | EOL 
        {Eol}
    | ENDEXPR 
        {Eol}
    | let_defs ENDEXPR
        {$1}
    | let_defs 
        {$1}
    | OPEN FILE_NAME ENDEXPR 
        {Open($2, Parsing.rhs_start_pos 1)}
    | prog ENDEXPR                
        { $1 }  
    | type_declaration ENDEXPR
        { $1 }


identifier:
    | IDENT     
        {Ident($1, Parsing.rhs_start_pos 1)}

int_atom:
    | INT               
        { Const $1 }
atoms:
    | UNDERSCORE
        { Underscore }
    | LPAREN RPAREN
        { Unit }
    | identifier
        {$1}
    | int_atom 
        { $1 }
    | TRUE 
        {Bool true}
    | FALSE 
        {Bool false}
    | CONSTRUCTOR  
        { Constructor_noarg($1, Parsing.rhs_start_pos 1) }

pattern_without_constr:
    | atoms
        { $1 }
    | LPAREN pattern_tuple RPAREN
        { $2 }
pattern_with_constr:
    | pattern_without_constr
        { $1 }
    | CONSTRUCTOR pattern_without_constr
        { Constructor($1, $2, Parsing.rhs_start_pos 1) }

pattern_tuple :
    | pattern_tuple_aux
        {match $1 with
        | [x] -> x
        | l -> Tuple (l, Parsing.rhs_start_pos 1)}
pattern_tuple_aux:
    | pattern_with_constr
        {[$1]}
    | pattern_with_constr COMMA pattern_tuple_aux
        {$1 :: $3}
fun_args_def:
    | RPAREN CONSTRUCTOR pattern_without_constr LPAREN
        { [(Constructor($2, $3, Parsing.rhs_start_pos 2), Parsing.rhs_start_pos 1)] }
    | pattern_without_constr 
        { [($1, Parsing.rhs_start_pos 1)] }
    | fun_args_def RPAREN CONSTRUCTOR pattern_without_constr LPAREN 
        { (Constructor($3, $4, Parsing.rhs_start_pos 3), Parsing.rhs_start_pos 3) :: $1 }
    | fun_args_def pattern_without_constr
        { ($2, Parsing.rhs_start_pos 2) :: $1 }


expr_atom:
    | atoms
        { $1 }
    | REF expr_atom
        {Ref ($2, Parsing.rhs_start_pos 1)}
    | array_type
        { $1 }
    | LPAREN prog RPAREN
       { $2 } 
funccall:
    | expr_atom 
        {$1}
    | funccall expr_atom 
        {Call($1, $2, Parsing.rhs_start_pos 2)}



types_atoms:
    | INT_TYPE
        { Int_type }
    | ARRAY_TYPE
        { Array_type }
    | BOOL_TYPE
        { Bool_type }
    | UNIT_TYPE
        { Unit_type }
    | polymorphic_type
        { $1 }

polymorphic_type:
    | POL_TYPE
        { Polymorphic_type $1}
types_tuple:
    | types_tuple_aux 
        { let l = List.rev $1
        in match l with
        | [x] -> x
        | l -> Tuple_type l}
types_tuple_aux:
    | types
        { [$1] }
    | types_tuple_aux TIMES types
        { $3 :: $1 }
types:
    | types_atoms
        {$1}
    | types ARROW types
        {Fun_type($1, $3)}
    | LPAREN types_tuple RPAREN
        {$2}
    | types_params
        {$1}

types_params:
    | IDENT 
        {Called_type($1, No_type 0)}
    | types IDENT
        {Called_type($2, Params_type ([$1]))}
    | LPAREN types_params_aux RPAREN IDENT
        { let l = List.rev $2
        in Called_type($4, Params_type l)}
types_params_aux:
    | types_tuple COMMA types_tuple
        { [$3; $1] }
    | types_params_aux COMMA types_tuple
        { $3 :: $1 }

types_params_def:
    | IDENT 
        {Called_type($1, No_type 0)}
    | polymorphic_type IDENT
        {Called_type($2, Params_type([$1]))}
    | LPAREN types_params_def_aux RPAREN IDENT
        { let l = List.rev $2
        in Called_type($4, Params_type l)}
types_params_def_aux:
    | polymorphic_type COMMA polymorphic_type
        { [$3; $1] }
    | types_params_def_aux COMMA polymorphic_type
        { $3 :: $1 }



constructor_declaration:
    | CONSTRUCTOR OF types_tuple
        { Constructor_type($1, Unit_type, $3) }
    | CONSTRUCTOR
        { Constructor_type_noarg($1, Unit_type) }

type_declaration_list:
    | constructor_declaration
        {[$1]}
    | DISJ constructor_declaration
        {[$2]}
    | type_declaration_list DISJ constructor_declaration
       {$3::$1}

type_declaration:
    | TYPE types_params_def EQUAL type_declaration_list
        {transfo_typedecl(TypeDecl($2, List.rev $4, Parsing.rhs_start_pos 1))}

    

let_defs:
    | LET pattern_tuple EQUAL prog 
        {Let($2, $4 , Parsing.rhs_start_pos 1)}
    | LET REC identifier EQUAL prog
        {Let($3, $5, Parsing.rhs_start_pos 1)}
    | LET identifier fun_args_def EQUAL prog
        {Let($2, List.fold_left (fun a (b, c) -> Fun(b, a, c)) $5 $3, Parsing.rhs_start_pos 1)}
    | LET REC identifier fun_args_def EQUAL prog
        {LetRec($3, List.fold_left (fun a (b, c) -> Fun(b, a, c)) $6 $4, Parsing.rhs_start_pos 1)}




arithmetics_expr:
    | prog PLUS prog          
        { BinOp(addOp, $1,$3, Parsing.rhs_start_pos 2) }
    | prog TIMES prog         
        { BinOp(multOp, $1,$3, Parsing.rhs_start_pos 2) }
    | prog DIV prog         
        { BinOp(divOp, $1,$3, Parsing.rhs_start_pos 2) }
    | prog MINUS prog         
        { BinOp(minusOp, $1,$3, Parsing.rhs_start_pos 2) }
    | prog OR prog         
        { BinOp(orOp, $1,$3, Parsing.rhs_start_pos 2) }
    | prog AND prog         
        { BinOp(andOp, $1,$3, Parsing.rhs_start_pos 2) }
    | prog SLT prog         
        { BinOp(sltOp, $1,$3, Parsing.rhs_start_pos 2) }
    | prog LT prog         
        { BinOp(ltOp, $1,$3, Parsing.rhs_start_pos 2) }
    | prog SGT prog         
        { BinOp(sgtOp, $1,$3, Parsing.rhs_start_pos 2) }
    | prog GT prog                                      
        { BinOp(gtOp, $1,$3, Parsing.rhs_start_pos 2) }
    | MINUS prog %prec UMINUS                           
        { BinOp(minusOp, Const 0, $2, Parsing.rhs_start_pos 1) }
    | prog NEQUAL prog         
        { BinOp(neqOp, $1,$3, Parsing.rhs_start_pos 2) }
    | prog EQUAL prog         
        { BinOp(eqOp, $1,$3, Parsing.rhs_start_pos 2) }

prog:
    | arithmetics_expr 
        {$1}
    | PRINTIN prog          
        { Printin($2, Parsing.rhs_start_pos 1) }
    | AMAKE prog            
        { ArrayMake ($2, Parsing.rhs_start_pos 1) } 
    | prog  SEQ prog         
        {Seq($1, $3, Parsing.rhs_start_pos 2)}
    | FUN fun_args_def ARROW prog 
        {let d = Parsing.rhs_start_pos 1 
        in let l = List.map fst $2
        in List.fold_left (fun a b -> Fun(b, a, d)) (Fun(List.hd l, $4, d)) (List.tl l)}
    | let_defs IN prog
        {In($1, $3, Parsing.rhs_start_pos 2)}
    | IF prog THEN prog %prec IFFINAL 
        {IfThenElse($2, $4, Unit ,Parsing.rhs_start_pos 1)}
    | IF prog THEN prog ELSE prog 
        {IfThenElse($2, $4, $6 ,Parsing.rhs_start_pos 1)}
    | BEGIN prog END                                    
        {$2}
    | TRY prog WITH E identifier ARROW prog
        {TryWith($2, $5, $7, Parsing.rhs_start_pos 1)}
    | TRY prog WITH E int_atom ARROW prog
        {TryWith($2, $5, $7, Parsing.rhs_start_pos 1)}
    | MATCH prog WITH match_list
        {MatchWith($2, List.rev $4, Parsing.rhs_start_pos 1)}
    | prog REFLET prog 
        {BinOp(refSet, $1, $3, Parsing.rhs_start_pos 2)}
    | RAISE prog 
        {Raise ($2, Parsing.rhs_start_pos 1)}
    | BANG prog 
        {Bang($2, Parsing.rhs_start_pos 1)}
    | NOT prog 
        {Not($2, Parsing.rhs_start_pos 1)}
    | funccall 
        {$1} 
    | tuple %prec below_COMMA
        {match $1 with
        | [x] -> x
        | l -> Tuple (List.rev l, Parsing.rhs_start_pos 1)} 
    | array_type ARRAYAFFECTATION prog 
        {match ($1) with
        | ArrayItem (x, y, _) -> ArraySet(x, y, $3, Parsing.rhs_start_pos 2)
        | _ -> failwith "error"}


match_list:
    | pattern_tuple ARROW prog
        {[($1, $3)]}
    | DISJ pattern_tuple ARROW prog
        {[($2, $4)]}
    | match_list DISJ pattern_tuple ARROW prog
       {($3, $5)::$1}
array_type :
    | LPAREN prog RPAREN DOT LPAREN prog RPAREN 
        {ArrayItem($2, $6, Parsing.rhs_start_pos 1)}
    | identifier  DOT LPAREN prog RPAREN 
        {ArrayItem($1, $4, Parsing.rhs_start_pos 1)}


tuple:
    | prog COMMA prog
        { [$3; $1] }
    | tuple COMMA prog
        { $3 :: $1 }


