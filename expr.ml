open Binop 
open Errors

let int_of_bool b =
  if b then 1 else 0

type identifier = string list * string
type 'a perhaps =
  | None
  | Some of 'a
(* structure for types *)
type type_listing =
  | Int_type
  | Bool_type
  | Array_type of type_listing
  | Unit_type
  | Var_type of tv ref
  | Ref_type of type_listing
  | Fun_type of type_listing * type_listing
  | Tuple_type of type_listing list
  | Constructor_type of identifier * type_listing * type_listing perhaps (* a constructor has a name, a father, and a type *)

  | Generic_type    of int
  | Polymorphic_type    of string (*for a polymoric type *)
  | Called_type         of identifier * int * type_listing list (* for types like ('a, 'b) expr *)

and tv = Unbound of int * int | Link of type_listing


let rec type_equal a b = match (a, b) with
  | Array_type l, Array_type l' -> type_equal l l'
  | Tuple_type l, Tuple_type l' -> List.for_all2 type_equal l l'
  | Generic_type l, Generic_type l' -> l = l'
  | Polymorphic_type l, Polymorphic_type l' -> l = l'
  | Fun_type (a, b), Fun_type (a', b') -> type_equal a a' && type_equal b b'
  | Ref_type l, Ref_type l' -> type_equal l l'
  | x, x' -> if x = x' then true else false

type sum_type =
  | CType_cst of string 
  | CType       of string * type_listing
type user_defined_types =
  | Renamed_decl of type_listing
  | Sum_decl    of type_listing
  | Constructor_decl of type_listing 


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
  | Constructor of identifier * 'a expr perhaps * Lexing.position (* a type represeting a construction in the form Constructor (name,parent, value) *)
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
  | Module of string * 'a expr * Lexing.position



  (* used for de bruijn indices preprocess *)
  | Access of int
  | Lambda of 'a expr
  | LambdaR of 'a expr
  | LetIn of 'a expr * 'a expr
  | LetRecIn of 'a expr * 'a expr
  | Bclosure of ('a code Dream.DreamEnv.item -> 'a code Dream.DreamEnv.item)
  | LetTup of 'a expr * 'a expr  (* could use Let instead of this, but less understandable *)
  | LetInTup of 'a expr * 'a expr * 'a expr (* really need for now because of compilB specifics *)

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
  | DUPL
  | SWAP
  | MATCH of int
  | PUSHMARK
  | UNFOLD
  | CONS

and 'a code = 'a instr list


(* manipulating ast in secd *)

let is_tup a = match a with
  | Tuple _ -> true
  | _ -> false

  let extr_tup a = match a with
  | Tuple (l, _) -> l
  | _ -> failwith "Expression is not a tuple."


(* printing functions *)

let rec print_code code line_jump =
  match code with
  | [] -> ""
  | [i] -> print_instr i
  | i::q -> print_instr i ^ (if line_jump then "\n--" else "") ^ print_code q line_jump

and print_instr i =
  match i with
  | C k -> Printf.sprintf " CONST(%s);" @@ string_of_int k
  | BOP bop -> " " ^ bop # symbol ^ ";"
  | ACCESS s -> Printf.sprintf " ACCESS(%s);" s
  | ACC i -> Printf.sprintf " ACC(%s);" (string_of_int i)
  | CLOSURE c -> Printf.sprintf " CLOSURE(%s);" (print_code c false)
  | CLOSUREC c -> Printf.sprintf " CLOSUREC(%s);" (print_code c false)
  | BUILTIN x -> " BUILTIN " ^ ";"
  | LET -> " LET;"
  | ENDLET -> " ENDLET;"
  | RETURN -> " RETURN;"
  | APPLY -> " APPLY;"
  | TAILAPPLY -> " TAILAPPLY;"
  | PRINTIN -> " PRINTIN;"
  | BRANCH -> " BRANCH;"
  | PROG c -> Printf.sprintf " PROG(%s);" (print_code c false)
  | REF -> " REF;"
  | BANG -> " BANG;"
  | EXIT -> " EXIT;"
  | ARRITEM -> " ARRITEM;"
  | ARRSET -> " ARRSET;"
  | TRYWITH -> " TRYWITH;"
  | UNIT -> " UNIT;"
  | PASS -> " PASS;"
  | PUSHMARK -> " PUSHMARK;"
  | CONS -> " CONS;"
  | UNFOLD -> " UNFOLD;"
  | _ -> Printf.sprintf " not implemented;"


let string_of_ident (l, n) =
   List.fold_left (fun a b -> a ^ b ^ "." )  "" l ^ n

let ident_equal i j =
  match (i, j) with
  | Ident(a, _), Ident(b, _) when a = b -> true
  | _ -> false


let get_operator_name node =
  match node with
  | Call(Call(Ident((l, n), _), _, _), _, _) when is_infix_operator n -> string_of_ident (l, n)
  | Call(Ident((l, n), _), _, _) when is_prefix_operator n -> string_of_ident (l, n)
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
  | Tuple (l, _) -> Printf.sprintf "Tuple [%s]" (List.fold_left (fun a b -> a ^ "; " ^ (show_expr b)) "" l) 
  | Access _ -> "access"
  | Lambda _ -> "lambda"
  | LambdaR _ -> "lambdaR"
  | LetIn _ -> "letin"
  | LetRecIn _-> "letrecin"
  | TypeDecl _ -> "type decl"
  | _ -> "too many expr"

