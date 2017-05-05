open Binop 
open Errors

let int_of_bool b =
  if b then 1 else 0

type identifier = string list * string
(* structure for types *)
type type_listing =
  | No_type of int
  | Int_type
  | Bool_type
  | Array_type of type_listing
  | Arg_type of type_listing
  | Unit_type
  | Var_type of tv ref
  | Ref_type of type_listing
  | Fun_type of type_listing * type_listing
  | Tuple_type of type_listing list
  | Constructor_type of string * type_listing * type_listing  (* a constructor has a name, a father, and a type *)
  | Constructor_type_noarg of string * type_listing  (* a constructor has a name, a father, and a type *)

  | Generic_type    of int
  | Polymorphic_type    of string (*for a polymoric type *)
  | Called_type         of string * type_listing list (* for types like ('a, 'b) expr *)

and tv = Unbound of int * int | Link of type_listing

type sum_type =
  | CType_cst of string 
  | CType       of string * type_listing
type user_defined_types =
  | Renamed_type of type_listing
  | Sum_type    of sum_type list


(* dealing with polymorphic types. We want every newly created to be different from the previous one *)
let current_pol_type = ref 0
(* get the next id corresponding to a polymorphic type *)
let new_generic_id () =
  let _ = incr current_pol_type 
  in !current_pol_type
(* new variable *)
let new_var level = begin
  Var_type (ref (Unbound (new_generic_id (), level)))
end

type type_declaration =
  | Constructor_list of type_listing list
  | Basic_type of type_listing

(* our ast *)
type 'a expr = 
  | Open of string * Lexing.position
  | Constructor of 'a expr * 'a expr *  Lexing.position (* a type represeting a construction in the form Constructor (name,parent, value) *)
  | Constructor_noarg of 'a expr *  Lexing.position (* a type represeting a construction in the form Constructor (name,parent, value) *)
  | TypeDecl of type_listing * type_declaration * Lexing.position
  | FixedType of 'a expr * type_listing * Lexing.position
  | Eol
  | Const     of int
  | Bool      of bool
  | Underscore 
  | ArrayItem of 'a expr * 'a expr * Lexing.position
  | ArraySet  of 'a expr * 'a expr * 'a expr * Lexing.position
  | Ident       of identifier * Lexing.position
  | Seq of 'a expr * 'a expr * Lexing.position
  | Unit
  | Not       of 'a expr * Lexing.position
  | In        of 'a expr * 'a expr * Lexing.position
  | MainSeq of 'a expr * 'a expr * Lexing.position (* this token is here uniquely to deal with file loading. It acts exactly like a seq *)
  | Let       of 'a expr * 'a expr  * Lexing.position
  | LetRec       of 'a expr * 'a expr * Lexing.position
  | Call      of 'a expr * 'a expr * Lexing.position
  | TryWith of 'a expr * 'a expr * 'a expr * Lexing.position
  | Raise of 'a expr * Lexing.position
  | Bang of 'a expr * Lexing.position
  | Ref of 'a expr * Lexing.position
  | IfThenElse of 'a expr * 'a expr * 'a expr * Lexing.position
  | RefLet of 'a expr * 'a expr * Lexing.position
  | Fun of 'a expr * 'a expr * Lexing.position
  | Printin of 'a expr * Lexing.position
  | ArrayMake of 'a expr * Lexing.position
  | BinOp of ('a, type_listing) binOp * 'a expr * 'a expr * Lexing.position
  | Tuple of 'a expr list * Lexing.position
  | MatchWith of 'a expr * ('a expr * 'a expr) list * Lexing.position
  (* used for de bruijn indices preprocess *)
  | Access of int
  | Lambda of 'a expr
  | LambdaR of 'a expr
  | LetIn of 'a expr * 'a expr
  | LetRecIn of 'a expr * 'a expr
  | Bclosure of ('a code Dream.DreamEnv.item -> 'a code Dream.DreamEnv.item)

(** SET OF INSTRUCTIONS FOR THE SECD MACHINE **)

and 'a instr =
  | C of int
  | BOP of ('a, type_listing) binOp
  | ACCESS of string
  | ACC of int (*specific to de bruijn *)
  | TAILAPPLY (* tail call optimization *)
  | CLOSURE of 'a code
  | CLOSUREC of 'a code 
  | BUILTIN of ('a code Dream.DreamEnv.item -> 'a code Dream.DreamEnv.item)
  | LET
  | ENDLET
  | APPLY
  | RETURN
  | PRINTIN (* affiche le dernier élément sur la stack, ne la modifie pas *)
  | BRANCH
  | PROG of 'a code
  | REF
  | AMAKE
  | ARRITEM
  | ARRSET
  | BANG 
  | TRYWITH
  | EXIT
  | PASS
  | EXCATCH
  | UNIT

and 'a code = 'a instr list



(* printing functions *)

let rec print_code code =
  match code with
  | [] -> ""
  | i::q -> print_instr i ^ print_code q

and print_instr i =
  match i with
  | C k -> Printf.sprintf " CONST(%s);" @@ string_of_int k
  | BOP bop -> " " ^ bop # symbol ^ ";"
  | ACCESS s -> Printf.sprintf " ACCESS(%s);" s
  | ACC i -> Printf.sprintf " ACC(%s);" (string_of_int i)
  | CLOSURE c -> Printf.sprintf " CLOSURE(%s);" (print_code c)
  | CLOSUREC c -> Printf.sprintf " CLOSUREC(%s);" (print_code c)
  | BUILTIN x -> " BUILTIN " ^ ";"
  | LET -> " LET;"
  | ENDLET -> " ENDLET;"
  | RETURN -> " RETURN;"
  | APPLY -> " APPLY;"
  | TAILAPPLY -> " TAILAPPLY;"
  | PRINTIN -> " PRINTIN;"
  | BRANCH -> " BRANCH;"
  | PROG c -> Printf.sprintf " PROG(%s);" (print_code c)
  | REF -> " REF;"
  | BANG -> " BANG;"
  | EXIT -> " EXIT;"
  | ARRITEM -> " ARRITEM;"
  | ARRSET -> "ARRSET; "
  | TRYWITH -> "TRYWITH; "
  | UNIT -> "UNIT; "
  | PASS -> "PASS; "
  | _ -> Printf.sprintf "not implemented;"


let string_of_ident ident =
  match ident with
  | Ident((l, n), _) -> List.fold_left (fun a b -> a ^ b ^ "." )  "" l ^ n
  | _ -> ""

let ident_equal i j =
  match (i, j) with
  | Ident(a, _), Ident(b, _) when a = b -> true
  | _ -> false


let get_operator_name node =
  match node with
  | Call(Call(Ident((l, n), _) as ident, _, _), _, _) when is_infix_operator n -> string_of_ident ident
  | Call(Ident((l, n), _) as ident, _, _) when is_prefix_operator n -> string_of_ident ident
  | _ -> ""

let is_node_operator node =
  match node with
  | Call(Call(Ident((_, n), _), _, _), _, _) when is_infix_operator n -> true
  | Call(Ident((_, n), _), _, _) when is_prefix_operator n -> true
  | _ -> false

(* interpretation function and type of an arithmetic operation *)



(* return true if expr is an 'atomic' expression *)
let is_atomic expr =
  match expr with
  | Bool _| Ident _ | Underscore | Const _ | Unit -> true
  | _ -> false

let rec show_expr e =
  match e with
  | Open _ -> "open"
  | Eol -> "eol"
  | Const _ -> "const"
  | Bool _ -> "bool"
  | Underscore -> "underscore"
  | ArrayItem _ -> "array item"
  | ArraySet _ -> "arr set"
  | Ident _ -> "ident"
  | Seq _ -> "seq"
  | Unit -> "unit"
  | Not _ -> "not"
  | In (a, b, _) -> Printf.sprintf "In (%s, %s)" (show_expr a) (show_expr b)
  | MainSeq _ -> "mainseq"
  | Let (a, b, _) -> Printf.sprintf "Let (%s, %s)" (show_expr a) (show_expr b)
  | LetRec _ -> "letrec"
  | Call (a, b, _) -> Printf.sprintf "Call (%s, %s)" (show_expr a) (show_expr b)
  | TryWith _ -> "trywwith"
  | Raise _ -> "raise"
  | Bang _ -> "bang"
  | Ref _ -> "ref"
  | IfThenElse _ -> "ifthenelse"
  | RefLet _ -> "reflet"
  | Fun _ -> "fun"
  | Printin _ -> "printin"
  | ArrayMake _ -> "arraymake"
  | BinOp _ -> "binop"
  | Tuple _ -> "tuple"
  | Access _ -> "access"
  | Lambda _ -> "lambda"
  | LambdaR _ -> "lambdaR"
  | LetIn _ -> "letin"
  | LetRecIn _-> "letrecin"
  | TypeDecl _ -> "type decl"
  | _ -> "too many expr"

