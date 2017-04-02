open Binop 
open Env
open Errors

let int_of_bool b =
  if b then 1 else 0
let bool_of_int x =
  if x = 0 then false
  else true
(*)
type debug_info = {
    pos_fname : string;
    pos_lnum : int;
    pos_bol : int;
    pos_cnum : int;
}
*)

type expr = 
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
    | Let       of expr * expr  * Lexing.position
    | LetRec       of expr * expr * Lexing.position
    | Call      of expr * expr * Lexing.position
    | TryWith of expr * expr * expr * Lexing.position
    | Raise of expr * Lexing.position
    | Bang of expr * Lexing.position
    | Ref of expr * Lexing.position
    | IfThenElse of expr * expr * expr * Lexing.position
    | RefLet of expr * expr * Lexing.position
(*    | Raise of expr
    | TryWith of expr * error * expr
  *)  | Fun of expr * expr * Lexing.position
    | Printin of expr * Lexing.position
    | ArrayMake of expr * Lexing.position
    | Closure of expr * expr * expr Env.t
    | ClosureRec of string * expr * expr * expr Env.t
    | BinOp of expr binOp * expr * expr * Lexing.position
                   

let action_wrapper_arithms action a b error_infos s = 
  match (a, b) with
  | Const x, Const y -> (Const ( action x y ))
  | _ -> raise (send_error ("This arithmetic operation (" ^ s ^ ") only works on integers") error_infos)


let action_wrapper_ineq action a b error_infos s =
  match (a, b) with
  | Const x, Const y -> Bool (action x y)
  | Bool x, Bool y -> Bool (action (int_of_bool x) (int_of_bool y))
  | _ -> raise (send_error ("This comparison operation (" ^ s ^ ") only works on objects of the same type") error_infos)

let action_wrapper_boolop action a b error_infos s =
  match (a, b) with
  | Bool x, Bool y -> Bool (action x y)
  | _ -> raise (send_error ("This boolean operation (" ^ s ^ ") only works on booleans") error_infos)

let action_reflet a b error_infos s =
  match (a) with 
  | RefValue(x) -> x := b; b
  | _ -> raise (send_error "Can't set a non ref value" error_infos)

let addOp = new binOp "+"  (action_wrapper_arithms (+))
let minusOp = new binOp "-"  (action_wrapper_arithms (-))
let multOp = new binOp "*" (action_wrapper_arithms ( * ))
let eqOp = new binOp "=" (action_wrapper_ineq (=))
let neqOp = new binOp "<>" (action_wrapper_ineq (<>))
let gtOp = new binOp ">=" (action_wrapper_ineq (>=))
let sgtOp = new binOp ">" (action_wrapper_ineq (>))
let ltOp = new binOp "<=" (action_wrapper_ineq (<=))
let sltOp = new binOp "<" (action_wrapper_ineq (<))
let andOp = new binOp "&&" (action_wrapper_boolop (&&))
let orOp = new binOp "||" (action_wrapper_boolop (||))

let refSet = new binOp ":=" action_reflet





let rec beautyfullprint program = 
    begin
     (* print_endline (colorate green "green");
      print_endline (colorate red "red");
      print_endline (colorate yellow "yellow");
      print_endline (colorate blue "blue");
      print_endline (colorate magenta "magenta");
      print_endline (colorate cyan "cyan");
      print_endline (colorate lightgray "lightgray");
      print_endline (colorate darkgray "darkgray");
      print_endline (colorate lightgreen "lightgreen");
      print_endline (colorate lightred "lightred");
      print_endline (colorate lightyellow "lightyellow");
      print_endline (colorate lightblue "lightblue");
      print_endline (colorate lightmagenta "lightmagenta");
      print_endline (colorate lightcyan "lightcyan");
      *)

  let rec aux program ident = 
    match program with
  | Const       (x)             -> colorate blue (string_of_int x)
  | Ident       (x, _)          -> x
  | Bool true                   -> colorate blue "true"
  | Bool false                  -> colorate blue "false"
  | Unit                        -> colorate blue "Unit"
  | Underscore                  -> "_"
  | BinOp (x, a, b, _)          -> x#print (aux a ident) (aux b ident)
  | In          (a, b, _)       -> 
        aux a ident ^
        "\n" ^ ident ^
        colorate green "in " ^
        aux b ident
  | Let         (a, b, _)       -> 
        colorate green "let " ^
        aux a ident ^
        colorate green " = " ^
        aux b ident
  | LetRec         (a, b, _)    -> 
        colorate green "let rec " ^
        aux a ident ^
        colorate green " = " ^
        aux b ident
  | Call        (a, b, _)       -> Printf.sprintf "%s (%s)" (aux a ident) (aux b ident)
  | IfThenElse  (a, b, c, _)    -> 
        "\n" ^ ident ^
        colorate green "if " ^
        aux a (ident ^ "  ") ^
        colorate green " then\n" ^
        ident ^ "  " ^
        aux b (ident ^ "  ") ^
        ident ^ colorate green "\nelse\n" ^
        ident ^ "  " ^
        aux c (ident ^ "  ")  
  | Fun         (a, b, _)       -> Printf.sprintf "%s %s (%s)" (aux a ident) (colorate lightyellow "->") (aux b ident)
  | Ref         (x, _)          -> Printf.sprintf "%s (%s)" (colorate lightblue "ref") (aux x ident) 
  | Raise       (x, _)          -> Printf.sprintf "%s (%s)" (colorate red "raise") (aux x ident)
  | TryWith     (a, b, c, _)    -> Printf.sprintf "\n%stry\n%s\n%swith E %s ->\n%s\n"
      ident (aux a (ident^"  ")) ident (aux b ident) (aux c (ident ^ "  "))
  | RefLet      (a, b, _)       -> Printf.sprintf "%s %s %s" (aux a ident) (colorate lightblue ":=") (aux b ident)
  | Bang        (x, _)          -> Printf.sprintf "%s%s" (colorate lightblue "!") (aux x ident)
  | Not        (x, _)           -> Printf.sprintf "not %s" (aux x ident)
  | Closure (id, expr, _)       ->Printf.sprintf "Closure(%s, %s)" (aux id ident) (aux expr ident)
  | ClosureRec (_, id, expr, _) ->Printf.sprintf "ClosureRec(%s, %s)" (aux id ident) (aux expr ident)
  | Printin (expr, p)           -> Printf.sprintf "%s (%s)"  (colorate yellow "prInt") (aux expr ident)
  | ArrayMake (expr, _)         -> Printf.sprintf "%s (%s)" (colorate yellow "aMake") (aux expr ident)
  | ArrayItem (id, index, _)    -> Printf.sprintf "%s.(%s)" (aux id ident) (aux index ident)
  | ArraySet (id, x, index, p)  -> Printf.sprintf "%s <- (%s)" (aux (ArrayItem(id, x, p)) ident) (aux index ident)
  | Seq (a, b, _)               -> 
        colorate green "begin\n" ^
        aux a (ident ^ "  ") ^
        aux b (ident ^ "  ") ^
        colorate green "end\n"
    
  | _ -> raise (InterpretationError "not implemented this thing for printing")

  in aux program ""
    end
