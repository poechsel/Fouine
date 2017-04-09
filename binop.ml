open Env

class ['e, 'b] binOp (print_symbol : string) (prec : int) (action : 'e -> 'e -> Lexing.position -> string -> 'e) (type_check: unit -> 'b ) = object

  method print a b = Printf.sprintf "%s %s %s" a print_symbol b
  method precedence = prec
  method symbol = print_symbol

  method act a b = action a b Lexing.dummy_pos "" 

  method interpret a b error = (action a b error print_symbol) 

  method type_check = type_check 

end ;;


