open Env
open Errors

class ['e] binOp (print_symbol : string) (action : 'e -> 'e -> Lexing.position -> string -> 'e)  = object

  method print a b = Printf.sprintf "(%s) %s (%s)" a (colorate green print_symbol) b

  method symbol = print_symbol

  method interpret a b error = (action a b error print_symbol) 

end ;;


