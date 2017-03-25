open Expr
open Parser

let _ = print_endline "fouine interpreter"
let _ = print_endline (if (let x = true in x && x) then "test" else "fail")
(*
let g x y = x - y
let g' = fun x -> fun y -> x - y
let _ = print_int (g 4 2)
let _ = print_endline ""
let _ = print_int (g' 4 2)
let h a b () = a + b
               *)

let lexbuf = Lexing.from_channel stdin

(* on enchaîne les tuyaux: lexbuf est passé à Lexer.token,
   et le résultat est donné à Parser.main *)

let parse () = Parser.main Lexer.token lexbuf
let r = parse ()
let _ = print_endline @@ beautyfullprint r;
