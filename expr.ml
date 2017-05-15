open Binop 
open Errors
open Commons






(* our ast *)
type 'a expr = 
  | Open of string * Lexing.position
  | Constructor of identifier * 'a expr perhaps * Lexing.position (* a type represeting a construction in the form Constructor (name,parent, value) *)
  | TypeDecl of Types.types * Types.declaration * Lexing.position
  | FixedType of 'a expr * Types.types * Lexing.position
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
  | BinOp of ('a, Types.types) binOp * 'a expr * 'a expr * Lexing.position
  | Tuple of 'a expr list * Lexing.position
  | MatchWith of 'a expr * ('a expr * 'a expr) list * Lexing.position
  | Module of string * 'a expr list * Types.module_signature perhaps * Lexing.position
  | Value of 'a



  (* used for de bruijn indices preprocess *)
  | Access of int
  | Lambda of 'a expr
  | LambdaR of 'a expr
  | LetIn of 'a expr * 'a expr
  | LetRecIn of 'a expr * 'a expr
  | Bclosure of ('a code Dream.DreamEnv.item -> 'a code Dream.DreamEnv.item)
  | LetTup of 'a expr * 'a expr  (* could use Let instead of this, but less understandable *)
  | LetInTup of 'a expr * 'a expr * 'a expr (* really need for now because of compilB specifics *)

(** SET OF INSTRUCTIONS FOR THE SECD AND ZINC MACHINES **)

and 'a instr =
  | C of int
  | B of bool
  | BOP of ('a, Types.types) binOp
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
  (* ZINC SPECIFIC INSTRUCTIONS : UNUSED BY SECD MACHINE *)
  | GRAB
  | APPTERM
  | CUR of 'a code
  | DUMMY
  | UPDATE
  | PUSH

and 'a code = 'a instr list

(* manipulating ast in secd *)

let is_tup a = match a with
  | Tuple _ -> true
  | _ -> false

  let extr_tup a = match a with
  | Tuple (l, _) -> l
  | _ -> failwith "Expression is not a tuple."

let ident_equal i j =
  match (i, j) with
  | Ident(a, _), Ident(b, _) when a = b -> true
  | _ -> false


(* printing functions *)

let rec print_code code line_jump =
  match code with
  | [] -> ""
  | [i] -> let s = print_instr i in String.sub s 0 ((String.length s) -1)
  | i::q -> print_instr i ^ (if line_jump then "\n" else "") ^ print_code q line_jump

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
  | AMAKE -> " AMAKE;"
  | EXCATCH -> " EXCATCH;"
  | DUPL -> " DUPL;"
  | SWAP -> " SWAP;"
  | GRAB -> " GRAB;"
  | APPTERM -> " APPTERM;"
  | DUMMY -> " DUMMY;"
  | UPDATE -> " UPDATE;"
  | PUSH -> " PUSH;"
  | B b -> if b then " BOOL true;" else " BOOL false;"
  | MATCH i -> " MATCH;" ^ (string_of_int i)
  | CUR c -> Printf.sprintf " CUR(%s);" (print_code c false)



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
  | Module _ -> "module"
  | LetInTup _ -> "LetInTup"
  | LetTup _ -> "LetTup"
  | Bclosure _ -> "Bclosure"
