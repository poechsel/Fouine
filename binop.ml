open Env


class ['e] binOp (print_symbol : string) (action : 'e -> 'e -> 'e)  = object

  method print a b = Printf.sprintf "%s %s %s" a print_symbol b

  method symbol = print_symbol

  method interpret a b  = (action a b ) 

end ;;


