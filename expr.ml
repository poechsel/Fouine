
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
  | Array_type
  | Unit_type
  | Var_type of type_listing ref
  | Ref_type of type_listing
  | Fun_type of type_listing * type_listing
  | Tuple_type of type_listing list
  | Constructor_type of string * string * type_listing  (* a constructor has a name, a father, and a type *)
  | Constructor_type_noarg of string * string  (* a constructor has a name, a father, and a type *)
  
  | Polymorphic_type    of string (*for a polymoric type *)
  | Called_type         of string * type_listing (* for types like ('a, 'b) expr *)
  | Params_type         of type_listing list

(* dealing with polymorphic types. We want every newly created to be different from the previous one *)
let current_pol_type = ref 0
let get_new_pol_type () = begin
  let temp = !current_pol_type in
  current_pol_type := !current_pol_type + 1;
  (ref (No_type temp))
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



(* interpretation function and type of an arithmetic operation *)
let action_wrapper_arithms action a b error_infos s = 
  match (a, b) with
  | Const x, Const y -> (Const ( action x y ))
  | _ -> raise (send_error ("This arithmetic operation (" ^ s ^ ") only works on integers") error_infos)

let type_checker_arithms () = Fun_type(Int_type, Fun_type(Int_type, Int_type))


(* interpretation function and type of an operation dealing with ineqalities *)
let action_wrapper_ineq action a b error_infos s =
  match (a, b) with
  | Const x, Const y -> Bool (action x y)
  | Bool x, Bool y -> Bool (action (int_of_bool x) (int_of_bool y))
  | _ -> raise (send_error ("This comparison operation (" ^ s ^ ") only works on objects of the same type") error_infos)

let type_checker_ineq () =
  let new_type = Var_type (get_new_pol_type ())
  in
  Fun_type(new_type, Fun_type(new_type, Bool_type))

(* interpretation function and type of a boolean operation *)
let action_wrapper_boolop action a b error_infos s =
  match (a, b) with
  | Bool x, Bool y -> Bool (action x y)
  | _ -> raise (send_error ("This boolean operation (" ^ s ^ ") only works on booleans") error_infos)
let type_checker_boolop () =
  Fun_type(Bool_type, Fun_type(Bool_type, Bool_type))

(* interpretation function and type of a reflet *)
let action_reflet a b error_infos s =
  match (a) with 
  | RefValue(x) -> x := b; Unit
  | _ -> raise (send_error "Can't set a non ref value" error_infos)

let type_checker_reflet () = 
  let new_type = Var_type (get_new_pol_type ())
  in Fun_type(Ref_type(new_type), Fun_type(new_type, Unit_type))



(* all of our binary operators *)
let addOp = new binOp "+"  2 (action_wrapper_arithms (+)) type_checker_arithms
let minusOp = new binOp "-" 2  (action_wrapper_arithms (-)) type_checker_arithms
let multOp = new binOp "*" 1 (action_wrapper_arithms ( * )) type_checker_arithms
let divOp = new binOp "/" 1 (action_wrapper_arithms (/)) type_checker_arithms
let eqOp = new binOp "=" 4 (action_wrapper_ineq (=)) type_checker_ineq
let neqOp = new binOp "<>" 4 (action_wrapper_ineq (<>)) type_checker_ineq
let gtOp = new binOp ">=" 3 (action_wrapper_ineq (>=)) type_checker_ineq
let sgtOp = new binOp ">" 3 (action_wrapper_ineq (>)) type_checker_ineq
let ltOp = new binOp "<=" 3 (action_wrapper_ineq (<=)) type_checker_ineq
let sltOp = new binOp "<" 3 (action_wrapper_ineq (<)) type_checker_ineq
let andOp = new binOp "&&" 5 (action_wrapper_boolop (&&)) type_checker_boolop
let orOp = new binOp "||" 5 (action_wrapper_boolop (||)) type_checker_boolop

let refSet = new binOp ":=" 6 action_reflet type_checker_reflet



(* return true if expr is an 'atomic' expression *)
let is_atomic expr =
  match expr with
  | Bool _| Ident _ | Underscore | Const _ | RefValue _ | Unit -> true
  | _ -> false


