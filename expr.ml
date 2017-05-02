
open Binop 
open Env
open Errors

let int_of_bool b =
  if b then 1 else 0

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

(* dealing with polymorphic types. We want every newly created to be different from the previous one *)
let current_pol_type = ref 0
let new_generic_id () =
  let _ = incr current_pol_type 
  in !current_pol_type

let new_var level = begin
  Var_type (ref (Unbound (new_generic_id (), level)))
end


(* our ast *)
type expr = 
  | Open of string * Lexing.position
  | SpecComparer of type_listing
  | Constructor of string * expr *  Lexing.position (* a type represeting a construction in the form Constructor (name,parent, value) *)
  | Constructor_noarg of string *  Lexing.position (* a type represeting a construction in the form Constructor (name,parent, value) *)
  | TypeDecl of type_listing * type_listing list * Lexing.position
  | Eol
  | Const     of int
  | Bool      of bool
  | Underscore 
  | Array     of int array
  | ArrayItem of expr * expr * Lexing.position
  | ArraySet  of expr * expr * expr * Lexing.position
  | RefValue of expr ref
  | Ident       of string * Lexing.position
  | Seq of expr * expr * Lexing.position
  | Unit
  | Not       of expr * Lexing.position
  | In        of expr * expr * Lexing.position
  | MainSeq of expr * expr * Lexing.position (* this token is here uniquely to deal with file loading. It acts exactly like a seq *)
  | Let       of expr * expr  * Lexing.position
  | LetRec       of expr * expr * Lexing.position
  | Call      of expr * expr * Lexing.position
  | TryWith of expr * expr * expr * Lexing.position
  | Raise of expr * Lexing.position
  | Bang of expr * Lexing.position
  | Ref of expr * Lexing.position
  | IfThenElse of expr * expr * expr * Lexing.position
  | RefLet of expr * expr * Lexing.position
  | Fun of expr * expr * Lexing.position
  | Printin of expr * Lexing.position
  | ArrayMake of expr * Lexing.position
  | Closure of expr * expr * (expr, type_listing) Env.t
  | ClosureRec of string * expr * expr * (expr, type_listing) Env.t
  | BuildinClosure of (expr -> Lexing.position -> expr) 
  | BinOp of (expr, type_listing) binOp * expr * expr * Lexing.position
  | Tuple of expr list * Lexing.position
  | MatchWith of expr * (expr * expr) list * Lexing.position
  (* used for de bruijn indices preprocess *)
  | Access of int
  | Lambda of expr
  | LambdaR of expr
  | LetIn of expr * expr
  | LetRecIn of expr * expr
  | Bclosure of string


let get_operator_name node =
  match node with
  | Call(Call(Ident(n, _), _, _), _, _) when is_infix_operator n -> n
  | Call(Ident(n, _), _, _) when is_prefix_operator n -> n
  | _ -> ""

let is_node_operator node =
  match node with
  | Call(Call(Ident(n, _), _, _), _, _) when is_infix_operator n -> true
  | Call(Ident(n, _), _, _) when is_prefix_operator n -> true
  | _ -> false

(* interpretation function and type of an arithmetic operation *)
let action_wrapper_arithms action a b error_infos s = 
  match (a, b) with
  | Const x, Const y -> (Const ( action x y ))
  | _ -> raise (send_error ("This arithmetic operation (" ^ s ^ ") only works on integers") error_infos)

let type_checker_arithms = Fun_type(Int_type, Fun_type(Int_type, Int_type))


(* interpretation function and type of an operation dealing with ineqalities *)
let action_wrapper_ineq action a b error_infos s =
  match (a, b) with
  | Const x, Const y -> Bool (action x y)
  | Bool x, Bool y -> Bool (action (int_of_bool x) (int_of_bool y))
  | _ -> raise (send_error ("This comparison operation (" ^ s ^ ") only works on objects of the same type") error_infos)

let type_checker_ineq  =
  let new_type = Generic_type (new_generic_id ())
  in
  Fun_type(new_type, Fun_type(new_type, Bool_type))

(* interpretation function and type of a boolean operation *)
let action_wrapper_boolop action a b error_infos s =
  match (a, b) with
  | Bool x, Bool y -> Bool (action x y)
  | _ -> raise (send_error ("This boolean operation (" ^ s ^ ") only works on booleans") error_infos)
let type_checker_boolop  =
  Fun_type(Bool_type, Fun_type(Bool_type, Bool_type))

(* interpretation function and type of a reflet *)
let action_reflet a b error_infos s =
  match (a) with 
  | RefValue(x) -> x := b; Unit
  | _ -> raise (send_error "Can't set a non ref value" error_infos)

let type_checker_reflet  = 
  let new_type = Generic_type (new_generic_id ())
  in Fun_type(Ref_type(new_type), Fun_type(new_type, Unit_type))



(* all of our binary operators *)
let addOp = new binOp "+"  3 (action_wrapper_arithms (+)) type_checker_arithms
let minusOp = new binOp "-" 3  (action_wrapper_arithms (-)) type_checker_arithms
let multOp = new binOp "*" 4 (action_wrapper_arithms ( * )) type_checker_arithms
let divOp = new binOp "/" 4 (action_wrapper_arithms (/)) type_checker_arithms
let eqOp = new binOp "=" 2 (action_wrapper_ineq (=)) type_checker_ineq
let neqOp = new binOp "<>" 2 (action_wrapper_ineq (<>)) type_checker_ineq
let gtOp = new binOp ">=" 2 (action_wrapper_ineq (>=)) type_checker_ineq
let sgtOp = new binOp ">" 2 (action_wrapper_ineq (>)) type_checker_ineq
let ltOp = new binOp "<=" 2 (action_wrapper_ineq (<=)) type_checker_ineq
let sltOp = new binOp "<" 2 (action_wrapper_ineq (<)) type_checker_ineq
let andOp = new binOp "&&" 2 (action_wrapper_boolop (&&)) type_checker_boolop
let orOp = new binOp "||" 2 (action_wrapper_boolop (||)) type_checker_boolop

let refSet = new binOp ":=" 0 action_reflet type_checker_reflet



(* return true if expr is an 'atomic' expression *)
let is_atomic expr =
  match expr with
  | Bool _| Ident _ | Underscore | Const _ | RefValue _ | Unit -> true
  | _ -> false

let rec show_expr e =
  match e with
  | Open _ -> "open"
  | SpecComparer _ -> "spec comparer"
  | Eol -> "eol"
  | Const _ -> "const"
  | Bool _ -> "bool"
  | Underscore -> "underscore"
  | Array _ -> "array"
  | ArrayItem _ -> "array item"
  | ArraySet _ -> "arr set"
  | RefValue _ -> "refvalue"
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
  | Closure _ -> "closure"
  | ClosureRec _ -> "closureRec"
  | BuildinClosure _ -> "bdclosure"
  | BinOp _ -> "binop"
  | Tuple _ -> "tuple"
  | Access _ -> "access"
  | Lambda _ -> "lambda"
  | LambdaR _ -> "lambdaR"
  | LetIn _ -> "letin"
  | LetRecIn _-> "letrecin"
  | TypeDecl _ -> "type decl"
  | _ -> "too many expr"

