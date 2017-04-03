open Parser
open Expr
open Errors
open Env
open Interpret
(*open Compil*)
open Binop

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

let lexbuf = Lexing.from_channel stdin (*(open_in "test.fo")*)

(* on enchaîne les tuyaux: lexbuf est passé à Lexer.token,
   et le résultat est donné à Parser.main *)
(*
let parse () = Parser.main Lexer.token lexbuf
let r = parse ()
let _ = print_endline @@ beautyfullprint r
let res, _ = interpret r (fun x y -> x, y) (fun x y -> x, y)
let _ = print_endline @@ beautyfullprint res
*)

(*)
let ld = Lexing.dummy_pos
let e2 = In(Const 1, Const 2, Lexing.dummy_pos)
let e3 = Printin(BinOp(addOp,Const 1, Const 2, Lexing.dummy_pos), Lexing.dummy_pos)
let e4 = BinOp(addOp, BinOp(multOp, Const 5, Const 4, ld), BinOp(addOp, Const 1, Const 1, ld), ld)
let e5 = BinOp(multOp, Ident("10"), Const 1, ld)
let l2 = compile e3 
let _ = print_endline @@ print_code l2
let _ = print_endline @@ print_code (compile e5)
*)

let rec repl env = 

    let _ = print_string @@ colorate lightblue ">> "; flush stdout
    in let parse () = Parser.main Lexer.token lexbuf
    in let r = parse ()
    in let _ = print_endline @@ beautyfullprint r
    in  let env'  = begin
    try
    let res, env' = interpret r env (fun x y -> x, y) (fun x y -> x, y)
    in  let _ = print_endline @@ beautyfullprint res
    in env'
    with InterpretationError x -> let _ = print_endline x in env

end    in repl env'

let _ = repl (Env.create)

(*
let test () = begin
    let a = 4 in let  b = 8 in 4;
    let a = 4 in 8;
    a * 10 + b
end
let _ = print_int (test ())
*)
