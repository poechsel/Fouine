open Env

class ['e, 'b] binOp (print_symbol : string) (action : 'e -> 'e -> Lexing.position -> string -> 'e) (type_check: 'b -> 'b -> 'b) = object

  method print a b = Printf.sprintf "%s %s %s" a print_symbol b

  method symbol = print_symbol

  method act a b = action a b Lexing.dummy_pos ""

  method interpret a b error = (action a b error print_symbol) 

  method type_check a b = type_check a b

end ;;


