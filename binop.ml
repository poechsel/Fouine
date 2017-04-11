open Env

(* to avoid dealing with dozens of matching cases for binary operators, we represents every one of them with a class
   - each operators has a symbol
   - a precedence
   - an interpretation function
   - and a type
   *)
class ['e, 'b] binOp (print_symbol : string) (prec : int) (action : 'e -> 'e -> Lexing.position -> string -> 'e) (type_check: unit -> 'b ) = object

  method precedence = prec
  method symbol = print_symbol

  method act a b = action a b Lexing.dummy_pos "" 

  method interpret a b error = (action a b error print_symbol) 

  method type_check = type_check 

end ;;


