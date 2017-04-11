
open Binop 
open Env
open Errors

let int_of_bool b =
  if b then 1 else 0
let bool_of_int x =
  if x = 0 then false
  else true


type type_listing =
  | No_type of int
  | Int_type
  | Bool_type
  | Array_type
  | Unit_type
  | Var_type of type_listing ref
  | Ref_type of type_listing
  | Fun_type of type_listing * type_listing
let current_pol_type = ref 0
let get_new_pol_type () = begin
  let temp = !current_pol_type in
  current_pol_type := !current_pol_type + 1;
  (ref (No_type temp))
end


type expr = 
  | Open of string * Lexing.position
  | SpecComparer of type_listing
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
  | Closure of expr * expr * (expr, type_listing) Env.t
  | ClosureRec of string * expr * expr * (expr, type_listing) Env.t
  | BinOp of (expr, type_listing) binOp * expr * expr * Lexing.position

let is_type e = 
  match e with 
  | Const _ | Bool _ | Array _ | RefValue _ | Unit -> true
  | _ -> false
let get_debug_infos e =
  match e with
  | Closure _ | ClosureRec _ | Eol | SpecComparer _ | Underscore | Const _ | Bool _ | Array _ | RefValue _ | Unit -> Lexing.dummy_pos
  | Open (_, l) | BinOp(_, _, _, l) | ArrayMake (_, l) | Printin (_, l) | Fun (_, _, l) | RefLet (_, _, l) | IfThenElse (_, _, _, l) | Ref (_, l) | Bang(_, l) | Raise (_, l) | TryWith (_, _, _, l) | Call (_, _, l) | LetRec (_, _, l) | Let (_, _, l) | In(_, _, l) | Not (_, l) | Seq (_, _, l) | Ident (_, l) | ArraySet (_, _, _, l) | ArrayItem (_, _, l) -> l


let action_wrapper_arithms action a b error_infos s = 
  match (a, b) with
  | Const x, Const y -> (Const ( action x y ))
  | _ -> raise (send_error ("This arithmetic operation (" ^ s ^ ") only works on integers") error_infos)

let type_checker_arithms () = Fun_type(Int_type, Fun_type(Int_type, Int_type))


let action_wrapper_ineq action a b error_infos s =
  match (a, b) with
  | Const x, Const y -> Bool (action x y)
  | Bool x, Bool y -> Bool (action (int_of_bool x) (int_of_bool y))
  | _ -> raise (send_error ("This comparison operation (" ^ s ^ ") only works on objects of the same type") error_infos)

let type_checker_ineq () =
  let new_type = Var_type (get_new_pol_type ())
  in
  Fun_type(new_type, Fun_type(new_type, Bool_type))

let action_wrapper_boolop action a b error_infos s =
  match (a, b) with
  | Bool x, Bool y -> Bool (action x y)
  | _ -> raise (send_error ("This boolean operation (" ^ s ^ ") only works on booleans") error_infos)

let type_checker_boolop () =
  Fun_type(Bool_type, Fun_type(Bool_type, Bool_type))


let action_reflet a b error_infos s =
  match (a) with 
  | RefValue(x) -> x := b; b
  | _ -> raise (send_error "Can't set a non ref value" error_infos)

let type_checker_reflet () = 
  let new_type = Var_type (get_new_pol_type ())
  in Fun_type(Ref_type(new_type), Fun_type(new_type, Unit_type))




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

let is_printable_type expr = match expr with
  | Bool _ | RefValue _ | Const _ | Unit | Array _ -> true
  | _ -> false

let is_atomic expr =
  match expr with
  | Bool _| Ident _ | Underscore | Const _ | RefValue _ | Unit -> true
  | _ -> false



let rec print_binop program ident underlined_a underlined_b = 
  match program with
  | BinOp (op, a, b, _) ->
    let str_a  = pretty_print_aux a ident true
    in let str_a = match a with
        | BinOp(op', _, _, _) when op'#precedence <= op#precedence -> str_a
        | x when is_atomic x -> str_a
        | _ ->
          Printf.sprintf "(%s)" str_a
    in let str_b  = pretty_print_aux b ident true
    in let str_b = match b with
        | BinOp(op', _, _, _) when op'#precedence <= op#precedence -> str_b
        | x when is_atomic x -> str_b
        | _ ->
          Printf.sprintf "(%s)" str_b
    in Printf.sprintf "%s %s %s" (if not underlined_a then str_a else underline str_a) (op#symbol) (if not underlined_b then str_b else underline str_b)
  | _ -> ""


and break_line inline ident =
  if not inline then "\n"^ident else " "
and pretty_print_unop fun_name program color ident inline underlined = 
  let str_x = pretty_print_aux program ident inline
  in let str_x = if underlined then underline str_x else str_x
  in colorate color fun_name ^ (if is_atomic program then str_x else Printf.sprintf "(%s)" str_x)

and pretty_print_not x ident inline underlined =
  pretty_print_unop "not " x green ident inline underlined
and pretty_print_bang x ident inline underlined =
  pretty_print_unop "!" x green ident inline underlined
and pretty_print_amake x ident inline underlined =
  pretty_print_unop "aMake " x yellow ident inline underlined
and pretty_print_prInt x ident inline underlined =
  pretty_print_unop "prInt " x yellow ident inline underlined

and pretty_print_arrayitem program ident inline underlined_id underlined_index = 
  match program with
  | ArrayItem (id, index, _) ->
    let str_id = pretty_print_aux id ident inline
    in let str_index = pretty_print_aux index ident inline
    in 
    (if underlined_id then underline str_id else str_id) ^
    colorate green "." ^ "(" ^ 
    (if underlined_index then underline str_index else str_index) ^
    ")"
  | _ -> ""
and pretty_print_arrayset program ident inline underlined_expr = 
  match program with
  | ArraySet (id, x, value, p) ->
    let str_value = pretty_print_aux value ident inline
    in
    pretty_print_arrayitem (ArrayItem(id, x, p)) ident inline false false ^
    colorate green " <- " ^
    (if underlined_expr then underline str_value else str_value)
  | _ -> ""
and pretty_print_seq program ident inline =
  match program with
  | Seq (a, b, _) -> 
    let str_a = (match a with
        | Seq _ -> pretty_print_seq a ident inline
        | _ -> pretty_print_aux a ident inline
      ) 
    in let str_b = (match b with
        | Seq _ -> pretty_print_seq b ident inline
        | _ -> pretty_print_aux b ident inline
      )
    in 
    str_a ^ ";"^ 
    break_line inline ident ^
    str_b
  | _ -> ""

and pretty_print_aux program ident inline = 
  match program with
  | Const       (x)             -> colorate blue (string_of_int x)
  | Ident       (x, _)          -> x
  | RefValue (x)                -> 
    "ref: " ^ (pretty_print_aux !x ident inline)
  | Bool true                   -> colorate blue "true"
  | Bool false                  -> colorate blue "false"
  | Array x                     ->
    let len = Array.length x
    in let rec aux_ar i  = 
         if i >= len then ""
         else if i < 100 then
           string_of_int x.(i) ^ "; " ^ aux_ar (i+1) 
         else "..."
    in Printf.sprintf "[|%s|]" @@  aux_ar 0
  | Unit                        -> colorate blue "Unit"
  | Underscore                  -> "_"
  | BinOp (x, a, b, _)          -> print_binop program ident false false
  | In          (a, b, _)       -> 
    "("^pretty_print_aux a ident inline ^
    break_line inline ident ^
    colorate green "in " ^
    pretty_print_aux b ident inline^")"
  | Let         (a, b, _)       -> 
    colorate green "let " ^
    pretty_print_aux a ident inline ^
    colorate green " = " ^
    pretty_print_aux b ident inline
  | LetRec         (a, b, _)    -> 
    colorate green "let rec " ^
    pretty_print_aux a ident inline ^
    colorate green " = " ^
    pretty_print_aux b ident inline
  | Call        (a, b, _)       -> 
    let str_b = pretty_print_aux b ident inline
    in let str_b  = (if is_atomic b then str_b else Printf.sprintf "(%s)" str_b)
    in Printf.sprintf "(%s) %s" (pretty_print_aux a ident inline) str_b
  | IfThenElse  (a, b, c, _)    -> 
    break_line inline ident ^
    colorate green "if " ^
    pretty_print_aux a (ident ^ "  ") inline ^
    colorate green " then" ^
    break_line inline (ident ^ "  ") ^
    pretty_print_aux b (ident ^ "  ") inline ^
    break_line inline (ident) ^
    colorate green "else" ^
    break_line inline (ident ^ "  ") ^
    pretty_print_aux c (ident ^ "  ")  inline
  | Fun         (a, b, _)       -> 
    colorate green "fun " ^
    pretty_print_aux a (ident ^ "  ") inline ^ 
    colorate green " -> " ^ 
    break_line inline (ident ^ "  ") ^ 
    pretty_print_aux b (ident ^ "  ") inline
  | Ref         (x, _)          -> 
    colorate blue "ref " ^
    pretty_print_aux x ident inline
  | Raise       (x, _)          -> 
    colorate lightred "raise " ^
    pretty_print_aux x ident inline
  | TryWith     (a, b, c, _)    -> 
    colorate green "try" ^
    break_line inline (ident ^ "  ") ^
    pretty_print_aux a (ident ^ "  ") inline ^ 
    break_line inline ident ^
    colorate green "with " ^
    colorate lightred "E " ^
    pretty_print_aux b ident inline ^ 
    colorate green " ->" ^
    break_line inline (ident^"  ") ^
    pretty_print_aux c ident inline
  | RefLet      (a, b, _)       -> 
    pretty_print_aux a ident inline ^
    colorate green " = " ^
    pretty_print_aux b ident inline
  | Bang        (x, _)          -> 
    pretty_print_bang x ident inline false
  | Not        (x, _)           -> 
    pretty_print_not x ident inline false
  | Closure (id, expr, _)       -> "fun"
  | ClosureRec (_, id, expr, _) -> "fun"
  | Printin (expr, p)           -> 
    pretty_print_prInt expr ident inline false
  | ArrayMake (expr, _)         -> 
    pretty_print_amake expr ident inline false
  | ArrayItem (id, index, _)    -> 
    pretty_print_arrayitem program ident inline false false
  | ArraySet (id, x, index, p)  -> 
    pretty_print_arrayset program ident inline false
  | Seq (a, b, _)               -> 
    colorate green "begin" ^
      break_line inline (ident ^ "  ") ^
    pretty_print_seq program (ident^"  ") inline ^
      break_line inline ident ^
    colorate green "end" ^
    break_line inline ""
  | Eol -> ""
  | SpecComparer _ -> ""

  | Open _ -> "opezn"
  | Eol -> "eol"
  | _ -> ""(*raise (InterpretationError "not implemented this thing for printing")
             *)




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


    pretty_print_aux program "" false
  end
