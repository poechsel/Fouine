%{
(* --- préambule: ici du code Caml --- *)

open Buildins
open Expr   (* rappel: dans expr.ml: 
             type expr = Const of int | Add of expr*expr | Mull of expr*expr *)

let get_error_infos = Parsing.rhs_start_pos 

let rec transfo_poly_types tbl t =
    let aux = transfo_poly_types tbl in
    match t with
    | Ref_type x -> Ref_type (aux x)
    | Fun_type (a, b) -> Fun_type (aux a, aux b)
    | Tuple_type l -> Tuple_type (List.map aux l)
    | Called_type (n, t) -> Called_type (n, (List.map aux t))
    | Arg_type x -> Arg_type (aux x)
    | Polymorphic_type s ->
            if Hashtbl.mem tbl s then
                Generic_type (Hashtbl.find tbl s)
            else 
                let u = new_generic_id ()
                in (Hashtbl.add tbl s u; print_int u; print_endline "";Generic_type u)
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
%token LISTINSERT
%token RBRACKET
%token LBRACKET

%token <string> INFIX_OP_0
%token <string> INFIX_OP_1
%token <string> INFIX_OP_2
%token <string> INFIX_OP_3
%token <string> INFIX_OP_4

%token <string> PREFIX_OP

%token TYPE DISJ OF
%token INT_TYPE ARRAY_TYPE UNIT_TYPE BOOL_TYPE 
%token <string> POL_TYPE

/* precedence order of elements. Unfortunately, their wasn't enough time to fully test if these precedences are correct */
%nonassoc IFFINAL
%nonassoc IDENT
%left IN
%nonassoc below_SEQ
%left SEQ
%left LET
%nonassoc FUN
%nonassoc below_WITH
%nonassoc WITH
%nonassoc THEN
%nonassoc ELSE
%left DISJ
%right ARROW
%nonassoc below_COMMA
%left COMMA
%right REFLET
%right TRY
%right ARRAYAFFECTATION
%right RAISE
%left IF 
%left OR AND
%left SGT GT SLT LT NEQUAL EQUAL INFIX_OP_0
%right LISTINSERT
%right INFIX_OP_1
%left PLUS MINUS INFIX_OP_2
%left TIMES DIV  INFIX_OP_3
%right INFIX_OP_4
%nonassoc NOT
%nonassoc UMINUS  
%nonassoc REC
%nonassoc PRINTIN
%nonassoc AMAKE
%nonassoc DOT
%right REF
%right BANG
%right PREFIX_OP
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
    | OPEN FILE_NAME ENDEXPR 
        {Open($2, get_error_infos 1)}
    | let_defs ENDEXPR
        {$1}
    | seq_list ENDEXPR                
        { $1 }  
    | type_declaration ENDEXPR
        { $1 }


identifier:
    | IDENT     
        {Ident($1, get_error_infos 1)}

int_atom:
    | INT               
        { Const $1 }
    
operators_name:
    | PREFIX_OP 
        {Ident($1, get_error_infos 1)}
    | INFIX_OP_0
        {Ident($1, get_error_infos 1)}
    | INFIX_OP_1
        {Ident($1, get_error_infos 1)}
    | INFIX_OP_2
        {Ident($1, get_error_infos 1)}
    | INFIX_OP_3
        {Ident($1, get_error_infos 1)}
    | INFIX_OP_4
        {Ident($1, get_error_infos 1)}
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
        { Constructor_noarg($1, get_error_infos 1) }
    | LBRACKET RBRACKET
        {Constructor_noarg(list_none, get_error_infos 1)}
    | LPAREN operators_name RPAREN
        {$2}

pattern_list_expr_decl:
    | pattern_list_expr_decl SEQ pattern_with_constr 
        {($3, get_error_infos 3)::$1}
    | pattern_with_constr         { [$1, get_error_infos 1] }
pattern_list_expr:
    | pattern_with_constr LISTINSERT pattern_with_constr
        {Constructor(list_elt, Tuple([$1; $3], get_error_infos 2), get_error_infos 3)}
    | LBRACKET pattern_list_expr_decl RBRACKET
    {List.fold_left (fun a (b, error) ->
        Constructor(list_elt, Tuple([b; a], error), error)
    ) (Constructor_noarg(list_none, get_error_infos 1)) $2
    }


pattern_without_constr:
    | atoms
        { $1 }
    | LPAREN pattern_tuple RPAREN
        { $2 }
pattern_with_constr:
    | pattern_without_constr
        { $1 }
    | pattern_list_expr
    {$1}
    | CONSTRUCTOR pattern_without_constr
        { Constructor($1, $2, get_error_infos 1) }

pattern_tuple :
    | pattern_tuple_aux
        {match $1 with
        | [x] -> x
        | l -> Tuple (l, get_error_infos 1)}
pattern_tuple_aux:
    | pattern_with_constr
        {[$1]}
    | pattern_with_constr COMMA pattern_tuple_aux
        {$1 :: $3}
fun_args_def:
    | RPAREN CONSTRUCTOR pattern_without_constr LPAREN
        { [(Constructor($2, $3, get_error_infos 2), get_error_infos 1)] }
    | pattern_without_constr 
        { [($1, get_error_infos 1)] }
    | fun_args_def RPAREN CONSTRUCTOR pattern_without_constr LPAREN 
        { (Constructor($3, $4, get_error_infos 3), get_error_infos 3) :: $1 }
    | fun_args_def pattern_without_constr
        { ($2, get_error_infos 2) :: $1 }


expr_atom:
    | atoms
        { $1 }
    | REF expr_atom
        {Ref ($2, get_error_infos 1)}
    | array_type
        { $1 }
    | LPAREN prog RPAREN
       { $2 } 
    | LPAREN prog SEQ seq_list RPAREN
       { Seq($2, $4, get_error_infos 3) } 

    | expr_atom LISTINSERT expr_atom
        {Constructor(list_elt, Tuple([$1; $3], get_error_infos 2), get_error_infos 3)}
    | LBRACKET list_expr_decl RBRACKET
    {List.fold_left (fun a (b, error) ->
        Constructor(list_elt, Tuple([b; a], error), error)
    ) (Constructor_noarg(list_none, get_error_infos 1)) $2
    
    }


list_expr_decl:
    | list_expr_decl SEQ expr_atom 
        {($3, get_error_infos 3)::$1}
    | expr_atom         { [$1, get_error_infos 1] }

funccall:
    | expr_atom 
        {$1}
    | funccall expr_atom 
        {Call($1, $2, get_error_infos 2)}



types_atoms:
    | INT_TYPE
        { Int_type }
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
    | types_atoms ARRAY_TYPE
    { Array_type $1}
    | types_atoms REF
    { Ref_type $1}
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
        {Called_type($1, [])}
    | types IDENT
        {Called_type($2, [$1])}
    | LPAREN types_params_aux RPAREN IDENT
        { let l = List.rev $2
        in Called_type($4, l)}
types_params_aux:
    | types_tuple COMMA types_tuple
        { [$3; $1] }
    | types_params_aux COMMA types_tuple
        { $3 :: $1 }

types_params_def:
    | IDENT 
        {Called_type($1, [])}
    | polymorphic_type IDENT
        {Called_type($2, [$1])}
    | LPAREN types_params_def_aux RPAREN IDENT
        { let l = List.rev $2
        in Called_type($4, l)}
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
        {transfo_typedecl(TypeDecl($2, List.rev $4, get_error_infos 1))}


let_defs:
    | LET pattern_tuple EQUAL seq_list 
        {Let($2, $4 , get_error_infos 1)}
    | LET REC identifier EQUAL seq_list
        {Let($3, $5, get_error_infos 1)}
    | LET identifier fun_args_def EQUAL seq_list
        {Let($2, List.fold_left (fun a (b, c) -> Fun(b, a, c)) $5 $3, get_error_infos 1)}
    | LET REC identifier fun_args_def EQUAL seq_list
        {LetRec($3, List.fold_left (fun a (b, c) -> Fun(b, a, c)) $6 $4, get_error_infos 1)}



    | LET REC LPAREN operators_name RPAREN EQUAL seq_list
        {Let($4, $7, get_error_infos 1)}
    | LET LPAREN operators_name RPAREN fun_args_def EQUAL seq_list
        {Let($3, List.fold_left (fun a (b, c) -> Fun(b, a, c)) $7 $5, get_error_infos 1)}
    | LET REC LPAREN operators_name RPAREN fun_args_def EQUAL seq_list
        {LetRec($4, List.fold_left (fun a (b, c) -> Fun(b, a, c)) $8 $6, get_error_infos 1)}


        


arithmetics_expr:
    | prog PLUS prog          
        { BinOp(addOp, $1,$3, get_error_infos 2) }
    | prog TIMES prog         
        { BinOp(multOp, $1,$3, get_error_infos 2) }
    | prog DIV prog         
        { BinOp(divOp, $1,$3, get_error_infos 2) }
    | prog MINUS prog         
        { BinOp(minusOp, $1,$3, get_error_infos 2) }
    | prog OR prog         
        { BinOp(orOp, $1,$3, get_error_infos 2) }
    | prog AND prog         
        { BinOp(andOp, $1,$3, get_error_infos 2) }
    | prog SLT prog         
        { BinOp(sltOp, $1,$3, get_error_infos 2) }
    | prog LT prog         
        { BinOp(ltOp, $1,$3, get_error_infos 2) }
    | prog SGT prog         
        { BinOp(sgtOp, $1,$3, get_error_infos 2) }
    | prog GT prog                                      
        { BinOp(gtOp, $1,$3, get_error_infos 2) }
    | MINUS prog %prec UMINUS                           
        { BinOp(minusOp, Const 0, $2, get_error_infos 1) }
    | prog NEQUAL prog         
        { BinOp(neqOp, $1,$3, get_error_infos 2) }
    | prog EQUAL prog         
        { BinOp(eqOp, $1,$3, get_error_infos 2) }
    | prog INFIX_OP_4 prog
        { Call(Call(Ident($2, get_error_infos 2), $1, get_error_infos 2), $3, get_error_infos 2)}
    | prog INFIX_OP_3 prog
        { Call(Call(Ident($2, get_error_infos 2), $1, get_error_infos 2), $3, get_error_infos 2)}
    | prog INFIX_OP_2 prog
        { Call(Call(Ident($2, get_error_infos 2), $1, get_error_infos 2), $3, get_error_infos 2)}
    | prog INFIX_OP_1 prog
        { Call(Call(Ident($2, get_error_infos 2), $1, get_error_infos 2), $3, get_error_infos 2)}
    | prog INFIX_OP_0 prog
        { Call(Call(Ident($2, get_error_infos 2), $1, get_error_infos 2), $3, get_error_infos 2)}


seq_list:
    | prog %prec below_SEQ
        {$1}
    | prog SEQ seq_list
     {Seq($1, $3, get_error_infos 2)}

prog:
    | arithmetics_expr 
        {$1}
    | PRINTIN prog          
        { Printin($2, get_error_infos 1) }
    | AMAKE prog            
        { ArrayMake ($2, get_error_infos 1) } 
    | FUN fun_args_def ARROW seq_list 
        {let d = get_error_infos 1 
        in let l = List.map fst $2
        in List.fold_left (fun a b -> Fun(b, a, d)) (Fun(List.hd l, $4, d)) (List.tl l)}
    | let_defs IN seq_list
        {In($1, $3, get_error_infos 2)}
    | IF prog THEN prog %prec IFFINAL 
        {IfThenElse($2, $4, Unit ,get_error_infos 1)}
    | IF prog THEN prog ELSE prog 
        {IfThenElse($2, $4, $6 ,get_error_infos 1)}
    | BEGIN seq_list END                                    
        {$2}
    | TRY seq_list WITH E identifier ARROW seq_list
        {TryWith($2, $5, $7, get_error_infos 1)}
    | TRY seq_list WITH E int_atom ARROW seq_list
        {TryWith($2, $5, $7, get_error_infos 1)}
    | MATCH prog WITH match_list
        {MatchWith($2, List.rev $4, get_error_infos 1)}
    | prog REFLET prog 
        {BinOp(refSet, $1, $3, get_error_infos 2)}
    | RAISE prog 
        {Raise ($2, get_error_infos 1)}
    | BANG prog 
        {Bang($2, get_error_infos 1)}
    | NOT prog 
        {Not($2, get_error_infos 1)}
    | PREFIX_OP prog
        {Call(Ident($1, get_error_infos  1), $2, get_error_infos 1)}
    | funccall 
        {$1} 
    | tuple %prec below_COMMA
        {match $1 with
        | [x] -> x
        | l -> Tuple (List.rev l, get_error_infos 1)} 
    | array_type ARRAYAFFECTATION prog 
        {match ($1) with
        | ArrayItem (x, y, _) -> ArraySet(x, y, $3, get_error_infos 2)
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
        {ArrayItem($2, $6, get_error_infos 1)}
    | identifier  DOT LPAREN prog RPAREN 
        {ArrayItem($1, $4, get_error_infos 1)}


tuple:
    | prog COMMA prog
        { [$3; $1] }
    | tuple COMMA prog
        { $3 :: $1 }


