open Env

let operator_begin_symbols = ['!'; '$'; '%'; '&'; '*'; '+'; '-'; '/'; ':'; '<'; '='; '>'; '?'; '@'; '^'; '|'; '~']

let is_operator x =
  if String.length x == 0 then false
  else List.mem x.[0] operator_begin_symbols 

let is_prefix_operator x =
  if String.length x == 0 then false
  else 
  List.mem x.[0] ['!'; '~'; '?'] 

let is_infix_operator x =
  is_operator x && (not (is_prefix_operator x))

let get_operator_precedence x =
  let _ = print_endline @@ " -> " ^ x
  in let aux () = 
  let d = x.[0]
  in if x = ":=" then -1
  else if List.mem d ['='; '<'; '>'; '|'; '&'; '$'] then 0
  else if List.mem d ['@'; '^'] then 1
  else if List.mem d ['+'; '-'] then 2
  else if List.mem d ['*'; '/'; '%'] then 3
  else if String.length x > 0 && x.[0] == '*' && x.[1] == '*' then 4
  else 6
in let u = aux ()
in let _ = print_string @@ "prec" ^ (string_of_int u) ^ "\n"
in u


(* to avoid dealing with dozens of matching cases for binary operators, we represents every one of them with a class
   - each operators has a symbol
   - a precedence
   - an interpretation function
   - and a type
   *)
class ['e, 'b] binOp (print_symbol : string) (prec : int) (action : 'e -> 'e -> Lexing.position -> string -> 'e) (type_check: 'b ) = object

  method precedence = prec
  method symbol = print_symbol

  method act a b = action a b Lexing.dummy_pos "" 

  method interpret a b error = (action a b error print_symbol) 

  method type_check = type_check 

end ;;


