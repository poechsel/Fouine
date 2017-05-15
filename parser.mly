%{
(* --- préambule: ici du code Caml --- *)

open Buildins
open Expr   
open Shared

let get_error_infos = Parsing.rhs_start_pos 

(* allow us to convert inputted polymorphic type to internal polymorphic types *)
let rec transfo_poly_types tbl t =
    let aux = transfo_poly_types tbl in
    match t with
    | Ref_type x -> Ref_type (aux x)
    | Fun_type (a, b) -> Fun_type (aux a, aux b)
    | Tuple_type l -> Tuple_type (List.map aux l)
    | Called_type (n, z, t) -> Called_type (n, z, (List.map aux t))
    | Polymorphic_type s ->
            if Hashtbl.mem tbl s then
                Generic_type (Hashtbl.find tbl s)
            else 
                let u = Hashtbl.length tbl
                in (Hashtbl.add tbl s u;Generic_type u)
    | Constructor_type (n, a, Some b) ->
            Constructor_type (n, aux a, Some (aux b))
    | Constructor_type(n, a, None) ->
            Constructor_type (n, aux a, None)
    | _ -> t
let transform_type =
    let tbl = Hashtbl.create 0 
    in transfo_poly_types tbl


let transfo_module l =
    (List.map (fun x ->
            let tbl = Hashtbl.create 0
            in match x with
            | Val_entry (s, t) -> Val_entry (s, transfo_poly_types tbl t)
            | Type_entry (s, Some t) -> 
                    let _ = print_endline "transforming def" in
                    Type_entry (transfo_poly_types tbl s, Some (transfo_poly_types tbl t))
            | x -> x
            ) l)


(* map the previous functions to all constructors in a type declaration *)
let transfo_typedecl typedecl = 
    match typedecl with
    | TypeDecl (name, (Module_type l), er) ->
        TypeDecl(name, Module_type (transfo_module l), er)
    | TypeDecl (name, what, er) ->
            let tbl = Hashtbl.create 0
            in let what = match what with
            | Constructor_list lst -> Constructor_list (List.map (transfo_poly_types tbl) lst )
            | Basic_type t -> Basic_type (transfo_poly_types tbl t)
            in TypeDecl(transfo_poly_types tbl name, what, er)
    | _ -> typedecl




let restrict_buildins with_ =
    if !(Shared.buildins_activated) then
        with_
    else
        failwith "not implemented without buildins"

let use_buildins with_ without =
    if !(Shared.buildins_activated) then
        with_
    else without
let mk_binop (symbol, es) (a, ea) (b, eb) =
    Call(Call(Ident(([], symbol), get_error_infos es), a, get_error_infos ea), b, get_error_infos eb)
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
%token COLON
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
%token <string> MIDENT
%token UNDERSCORE
%token SEQ 
%token TRUE
%token FALSE
%token OPEN
%token MATCH 
%token LISTINSERT
%token RBRACKET
%token LBRACKET
%token MODULE
%token SIG
%token VAL
%token STRUCT

%token <string> INFIX_OP_0
%token <string> INFIX_OP_1
%token <string> INFIX_OP_2
%token <string> INFIX_OP_3
%token <string> INFIX_OP_4
%token <string> INFIX_OP_REF

%token <string> PREFIX_OP

%token TYPE DISJ OF
%token INT_TYPE ARRAY_TYPE UNIT_TYPE BOOL_TYPE 
%token <string> POL_TYPE

/* precedence order of elements. Unfortunately, their wasn't enough time to fully test if these precedences are correct */
%nonassoc IFFINAL
%nonassoc IDENT
%nonassoc below_SEQ
%left SEQ
%nonassoc WITH
%nonassoc ELSE
%left DISJ
%nonassoc below_COMMA
%left COMMA
%right ARROW
%right REFLET
%right ARRAYAFFECTATION INFIX_OP_REF
%left OR AND
%left SGT GT SLT LT NEQUAL EQUAL INFIX_OP_0
%right INFIX_OP_1
%left PLUS MINUS INFIX_OP_2
%right LISTINSERT
%left TIMES DIV  INFIX_OP_3
%right INFIX_OP_4
%nonassoc UMINUS  
%right PREFIX_OP

%start main             
                       
%type <((Shared.fouine_values) Expr.expr)> main

%%

main:                     
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

    | MODULE modules ENDEXPR
        { $2 }
/*
    | MODULE MIDENT EQUAL STRUCT END ENDEXPR
        { Module ($2, [], get_error_infos 1)}
    | MODULE MIDENT EQUAL STRUCT list_lines END ENDEXPR
        {Module($2, List.rev $5, get_error_infos 1) }
*/

/* modules */
modules:
    | TYPE MIDENT EQUAL modules_sig
        { TypeDecl (Called_type(([], $2), -1, []), Module_type $4, get_error_infos 1)}
    | MIDENT COLON modules_sig EQUAL modules_content
        { Module ($1, $5, Some (Unregister $3), get_error_infos 1)}
    | MIDENT COLON full_constructor_name EQUAL modules_content
        { Module ($1, $5, Some (Register $3), get_error_infos 1)}
    | MIDENT EQUAL modules_content
        { Module ($1, $3, None, get_error_infos 1)}

modules_content:
    | STRUCT END
        { [] }
    | STRUCT list_lines END 
        { List.rev $2}


module_sig_item:
    | VAL IDENT COLON types_expr ENDEXPR
        {Val_entry(([], $2), $4)}
    | TYPE types_params_def ENDEXPR
        {Type_entry($2, None)}
    | TYPE types_params_def EQUAL types_expr ENDEXPR
        {Type_entry($2, Some $4)}


module_items:
    | module_sig_item
        {[$1]}
    | module_sig_item module_items
        {$1::$2}

modules_sig:
    | SIG END
        { [] }
    | SIG module_items END
        { transfo_module $2 }



/* other things */

list_lines:
    | main
        { [$1] }
    | list_lines main
        { $2 :: $1 }

identifier_aux:
    | IDENT
        {([], $1)}
    | module_accesseur IDENT
        {($1, $2)}

/* types de donnés atomiques */
identifier:
    | identifier_aux 
        {Ident($1, get_error_infos 1)}
    | module_accesseur LPAREN operators_name RPAREN
        {Ident(($1, $3), get_error_infos 3)}
    | LPAREN operators_name RPAREN
        {Ident(([], $2), get_error_infos 2)}

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
    | full_constructor_name   
        { Constructor($1, None, get_error_infos 1) }
    | LBRACKET RBRACKET
        {Constructor(list_none, None, get_error_infos 1)}

/* parser les noms d'opérateurs customisés*/
operators_name:
    | PREFIX_OP 
        { $1 }
    | INFIX_OP_REF
        { $1 }
    | INFIX_OP_0
        { $1 }
    | INFIX_OP_1
        { $1 }
    | INFIX_OP_2
        { $1 }
    | INFIX_OP_3
        { $1 }
    | INFIX_OP_4
        { $1 }
    | PLUS   { restrict_buildins "+"  }
    | MINUS  { restrict_buildins "-"  }
    | TIMES  { restrict_buildins "*"  }
    | DIV    { restrict_buildins "/"  }
    | EQUAL  { restrict_buildins "="  }
    | LT     { restrict_buildins "<=" }
    | GT     { restrict_buildins ">=" }
    | SLT    { restrict_buildins "<"  }
    | SGT    { restrict_buildins ">"  }
    | NEQUAL { restrict_buildins "<>" }
    | OR     { restrict_buildins "||" }
    | AND    { restrict_buildins "&&" }



/******************************************** 
*            gérer les patterns 
********************************************/
pattern_list_expr_decl:
    | pattern_list_expr_decl SEQ pattern_with_constr 
        {($3, get_error_infos 3)::$1}
    | pattern_with_constr         { [$1, get_error_infos 1] }
pattern_list_expr:
    | pattern_with_constr LISTINSERT pattern_with_constr
        {Constructor(list_elt, Some (Tuple([$1; $3], get_error_infos 2)), get_error_infos 3)}
    | LBRACKET pattern_list_expr_decl RBRACKET
    {List.fold_left (fun a (b, error) ->
        Constructor(list_elt, Some (Tuple([b; a], error)), error)
    ) (Constructor(list_none, None, get_error_infos 1)) $2
    }

    

pattern_without_constr:
    | atoms
        { match $1 with 
            | Ident(([], _), _) -> $1
            | Ident _ -> failwith "erreur de syntace"
            | _ -> $1
        }
    | LPAREN pattern_tuple RPAREN
        { $2 }
pattern_with_constr:
    | pattern_without_constr
        { $1 }
    | pattern_list_expr
    {$1}
   | full_constructor_name pattern_without_constr
        { Constructor($1, Some $2, get_error_infos 1) }

pattern_tuple :
    | pattern_tuple_aux
        {match $1 with
        | [x] -> x
        | l -> Tuple (l, get_error_infos 1)}



pattern_tuple_aux:
    | LPAREN pattern_with_constr COLON types_expr RPAREN
        {[FixedType($2, $4, get_error_infos 3)]}
    | pattern_with_constr 
        {[$1]}
    | LPAREN pattern_with_constr COLON types_expr RPAREN COMMA pattern_tuple_aux
        {FixedType($2, $4, get_error_infos 3) :: $7}
    | pattern_with_constr COMMA pattern_tuple_aux
        {$1 :: $3}

module_accesseur:
    | MIDENT DOT
        {[$1]}
    | module_accesseur MIDENT DOT
        {$2 :: $1}

full_constructor_name:
    | MIDENT
        {([], $1)}
    | module_accesseur MIDENT
        {($1, $2)}

/* parser les arguments de fonctions lors de leurs déclarations */
fun_args_def:
    | LPAREN pattern_without_constr  COLON types_expr RPAREN
        { [(FixedType($2, transform_type $4, get_error_infos 3), get_error_infos 1)] }
    | pattern_without_constr 
        { [($1, get_error_infos 1)] }
    | fun_args_def pattern_without_constr
        { ($2, get_error_infos 2) :: $1 }
    | fun_args_def LPAREN pattern_without_constr  COLON types_expr RPAREN
        { (FixedType($3, transform_type $5, get_error_infos 4), get_error_infos 2) :: $1 }


/* expressions atomiques */
expr_atom:
    | atoms
        { $1 }
    | REF expr_atom
        {Ref ($2, get_error_infos 1)}
    | array_type
        { $1 }
    | LPAREN prog COLON types_expr RPAREN
        { FixedType($2, transform_type $4, get_error_infos 3)}
    | LPAREN prog RPAREN
       { $2 } 
    | LPAREN prog SEQ seq_list RPAREN
       { Seq($2, $4, get_error_infos 3) } 

    | LBRACKET list_expr_decl RBRACKET
    {List.fold_left (fun a (b, error) ->
        Constructor(list_elt, Some (Tuple([b; a], error)), error)
    ) (Constructor(list_none, None, get_error_infos 1)) $2
    
    }
    | BANG expr_atom
        {Bang($2, get_error_infos 1)}


list_expr_decl:
    | list_expr_decl SEQ expr_atom 
        {($3, get_error_infos 3)::$1}
    | expr_atom         { [$1, get_error_infos 1] }


/* parse des suites d'expressions atomiques. Sert pour les arguments / constantes */
funccall:
    | PRINTIN
        {Ident(([], "prInt"), get_error_infos 1)}
    | NOT
        {Ident(([], "not"), get_error_infos 1)}
    | AMAKE
        {Ident(([], "aMake"), get_error_infos 1)}
    | expr_atom 
        {$1}
    | funccall expr_atom 
        {match $1 with
        | Ident((_, "prInt"), _) ->
            use_buildins 
            (Call($1, $2, get_error_infos 2))
            (Printin($2, get_error_infos 1))
        | Ident((_, "not"), _) ->
            use_buildins 
            (Call($1, $2, get_error_infos 2))
            (Not($2, get_error_infos 1))
        | Ident((_, "aMake"), _) ->
            use_buildins 
            (Call($1, $2, get_error_infos 2))
            (ArrayMake($2, get_error_infos 1))
        | _ ->
        
        Call($1, $2, get_error_infos 2)}

identifier_with_constraint:
    | identifier
        { $1 }
    | LPAREN identifier COLON types_expr RPAREN
        { FixedType($2, $4, get_error_infos 3)}

/* expressions sous forme de lets.
On transforme les "let rec identifiant = ..." en "let identifiant = ..."*/
let_defs:
    | LET pattern_tuple EQUAL seq_list 
        {Let($2, $4 , get_error_infos 1)}
    | LET REC identifier EQUAL seq_list
        {LetRec($3, $5, get_error_infos 1)}
    | LET identifier fun_args_def EQUAL seq_list
        {Let($2, List.fold_left (fun a (b, c) -> Fun(b, a, c)) $5 $3, get_error_infos 1)}
    | LET REC identifier fun_args_def EQUAL seq_list
        {LetRec($3, List.fold_left (fun a (b, c) -> Fun(b, a, c)) $6 $4, get_error_infos 1)}

    | LET identifier fun_args_def COLON types_expr EQUAL seq_list
        {Let(
      FixedType($2, transform_type @@ Fun_type(Generic_type (new_generic_id ()), $5), get_error_infos 4), List.fold_left (fun a (b, c) -> Fun(b, a, c)) $7 $3,
get_error_infos 1) 
        }
    | LET pattern_tuple COLON types_expr EQUAL seq_list 
        {Let(FixedType($2, transform_type @@ $4, get_error_infos 3), $6 , get_error_infos 1)}

        

arithmetics_expr:
    | prog PLUS prog          
    { use_buildins
        (mk_binop ("+", 2) ($1, 2) ($3, 2))
        (BinOp(addOp, $1,$3, get_error_infos 2)) }
    | prog TIMES prog         
    { use_buildins
        (mk_binop ("*", 2) ($1, 2) ($3, 2))
        (BinOp(multOp, $1,$3, get_error_infos 2)) }
    | prog DIV prog         
    { use_buildins
        (mk_binop ("/", 2) ($1, 2) ($3, 2))
         (BinOp(divOp, $1,$3, get_error_infos 2)) }
    | prog MINUS prog         
    { use_buildins
        (mk_binop ("-", 2) ($1, 2) ($3, 2))
        (BinOp(minusOp, $1,$3, get_error_infos 2)) }
    | prog OR prog         
    { use_buildins
        (mk_binop ("||", 2) ($1, 2) ($3, 2))
        (BinOp(orOp, $1,$3, get_error_infos 2)) }
    | prog AND prog         
    { use_buildins
        (mk_binop ("&&", 2) ($1, 2) ($3, 2))
        (BinOp(andOp, $1,$3, get_error_infos 2)) }
    | prog SLT prog         
    { use_buildins
        (mk_binop ("<", 2) ($1, 2) ($3, 2))
        (BinOp(sltOp, $1,$3, get_error_infos 2)) }
    | prog LT prog         
    { use_buildins
        (mk_binop ("<=", 2) ($1, 2) ($3, 2))
        (BinOp(ltOp, $1,$3, get_error_infos 2)) }
    | prog SGT prog         
    { use_buildins
        (mk_binop (">", 2) ($1, 2) ($3, 2))
        (BinOp(sgtOp, $1,$3, get_error_infos 2)) }
    | prog GT prog                                      
    { use_buildins
        (mk_binop (">=", 2) ($1, 2) ($3, 2))
        (BinOp(gtOp, $1,$3, get_error_infos 2)) }
    | MINUS prog %prec UMINUS                           
    { use_buildins
        (mk_binop ("-", 2) (Const 0, 2) ($2, 2))
        (BinOp(minusOp, Const 0, $2, get_error_infos 1)) }
    | prog NEQUAL prog         
    { use_buildins
        (mk_binop ("<>", 2) ($1, 2) ($3, 2))
        (BinOp(neqOp, $1,$3, get_error_infos 2)) }
    | prog EQUAL prog         
    { use_buildins
        (mk_binop ("=", 2) ($1, 2) ($3, 2))
        (BinOp(eqOp, $1,$3, get_error_infos 2)) }
    | prog INFIX_OP_4 prog
        {mk_binop ($2, 2) ($1, 2) ($3, 2)}
    | prog INFIX_OP_3 prog
        {mk_binop ($2, 2) ($1, 2) ($3, 2)}
    | prog INFIX_OP_REF prog
        {mk_binop ($2, 2) ($1, 2) ($3, 2)}
    | prog INFIX_OP_2 prog
        {mk_binop ($2, 2) ($1, 2) ($3, 2)}
    | prog INFIX_OP_1 prog
        {mk_binop ($2, 2) ($1, 2) ($3, 2)}
    | prog INFIX_OP_0 prog
        {mk_binop ($2, 2) ($1, 2) ($3, 2)}

    | prog LISTINSERT prog
        {Constructor(list_elt, Some (Tuple([$1; $3], get_error_infos 2)), get_error_infos 3)}

seq_list:
    | prog %prec below_SEQ
        {$1}
    | prog SEQ seq_list
     {Seq($1, $3, get_error_infos 2)}

prog:
    | arithmetics_expr 
        {$1}
   /* | PRINTIN prog          
        { use_buildins 
            (Call(Ident(([], "prInt"), get_error_infos 1), $2, get_error_infos 2))
            (Printin($2, get_error_infos 1))
        }
    | AMAKE prog            
        { use_buildins 
            (Call(Ident(([], "aMake"), get_error_infos 1), $2, get_error_infos 2))
            (ArrayMake($2, get_error_infos 1))
        }
    | NOT expr_atom 
        { use_buildins 
            (Call(Ident(([], "not"), get_error_infos 1), $2, get_error_infos 2))
            (Not($2, get_error_infos 1))
        }
   */ | FUN fun_args_def ARROW seq_list 
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
    | TRY seq_list WITH E expr_atom ARROW seq_list
        {TryWith($2, $5, $7, get_error_infos 1)}
    | MATCH prog WITH match_list
        {MatchWith($2, List.rev $4, get_error_infos 1)}
    | prog REFLET prog 
        {BinOp(refSet, $1, $3, get_error_infos 2)}
    | RAISE LPAREN E expr_atom RPAREN
        {Raise ($4, get_error_infos 1)}
    | PREFIX_OP expr_atom
        {Call(Ident(([], $1), get_error_infos  1), $2, get_error_infos 1)}
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


/* expression match with */
match_list:
    | pattern_tuple ARROW prog
        {[($1, $3)]}
    | DISJ pattern_tuple ARROW prog
        {[($2, $4)]}
    | match_list DISJ pattern_tuple ARROW prog
       {($3, $5)::$1}

/* pour les tableaux */
array_type :
    | LPAREN prog RPAREN DOT LPAREN prog RPAREN 
        {ArrayItem($2, $6, get_error_infos 1)}
    | identifier  DOT LPAREN prog RPAREN 
        {ArrayItem($1, $4, get_error_infos 1)}
/* pour les tuples */
tuple:
    | prog COMMA prog
        { [$3; $1] }
    | tuple COMMA prog
        { $3 :: $1 }





/******************************************************************************
*           Parsing des type
******************************************************************************/


/* type polymorphique */
polymorphic_type:
    | POL_TYPE
        { Polymorphic_type $1}
/* types atomiques */
types_atoms:
    | INT_TYPE
        { Int_type }
    | BOOL_TYPE
        { Bool_type }
    | UNIT_TYPE
        { Unit_type }
    | polymorphic_type
        { $1 }

/* tuples de types */
types_tuple:
    | types_tuple_aux 
        { let l = List.rev $1
        in match l with
        | [x] -> x
        | l -> Tuple_type l}
types_tuple_aux:
    | types
        { [$1] }
    | types_tuple_aux INFIX_OP_3 types
        { if $2 = "*" then $3 :: $1 else failwith "bad thing" }
    | types_tuple_aux TIMES types
        { $3 :: $1 }

types_arrow_aux:
    | types ARROW types
        { Fun_type($1, $3) }
    | types ARROW types_arrow_aux
        { Fun_type($1, $3)}


/* la liste des types parsables */
types:
    | types_atoms ARRAY_TYPE
    { Array_type $1}
    | types_atoms REF
    { Ref_type $1}
    | types_atoms
        {$1}
    | LPAREN types_expr RPAREN
        { $2 }
    | types_params
        {$1}

/* parser les types paramétriques (de la forme ('a,...,'c) type) */
types_params:
    | identifier_aux 
        {Called_type($1, -1, [])}
    | types identifier_aux 
        {Called_type($2, -1, [$1])}
    | LPAREN types_params_aux RPAREN identifier_aux
        { let l = List.rev $2
        in Called_type($4, -1, l)}
    /*    
    | IDENT 
        {Called_type(([], $1), -1, [])}
    | types IDENT 
        {Called_type(([], $2), -1, [$1])}
    | LPAREN types_params_aux RPAREN IDENT
        { let l = List.rev $2
        in Called_type(([], $4), -1, l)}
      */


types_params_aux:
    | types_tuple COMMA types_tuple
        { [$3; $1] }
    | types_params_aux COMMA types_tuple
        { $3 :: $1 }

/* les définitions de types */
types_params_def:
    | IDENT 
        {Called_type(([], $1), -1, [])}
    | polymorphic_type IDENT
        {Called_type(([], $2), -1, [$1])}
    | LPAREN types_params_def_aux RPAREN IDENT
        { let l = List.rev $2
        in Called_type(([], $4), -1, l)}
types_params_def_aux:
    | polymorphic_type COMMA polymorphic_type
        { [$3; $1] }
    | types_params_def_aux COMMA polymorphic_type
        { $3 :: $1 }



constructor_declaration:
    | MIDENT OF types_tuple
        { Constructor_type(([], $1), Unit_type, Some $3) }
    | MIDENT
        { Constructor_type(([], $1), Unit_type, None) }

type_declaration_list:
    | constructor_declaration
        {[$1]}
    | DISJ constructor_declaration
        {[$2]}
    | type_declaration_list DISJ constructor_declaration
       {$3::$1}


types_expr:
    | types_arrow_aux
        { $1 }
    | types_tuple
        { $1 }

type_declaration:
    /* for expression in the form type test = foo -> bar;;
    *   otherwise we are parsing -> with paranthesis
    * */
    | TYPE types_params_def EQUAL types_arrow_aux
    /* for expression in the form type test = foo;;*/
        {transfo_typedecl(TypeDecl($2, Basic_type $4, get_error_infos 1))}
    | TYPE types_params_def EQUAL types_tuple
        {transfo_typedecl(TypeDecl($2, Basic_type $4, get_error_infos 1))}
    /* sum types */
    | TYPE types_params_def EQUAL type_declaration_list
        {transfo_typedecl(TypeDecl($2, Constructor_list (List.rev $4), get_error_infos 1))}
