open Parser
open Expr
open Errors
open Env
open Interpret
open Compil
open Binop
open Inference

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



(* on enchaîne les tuyaux: lexbuf est passé à Lexer.token,
   et le résultat est donné à Parser.main *)
(*
let parse () = Parser.main Lexer.token lexbuf
let r = parse ()
let _ = print_endline @@ beautyfullprint r
let res, _ = interpret r (fun x y -> x, y) (fun x y -> x, y)
let _ = print_endline @@ beautyfullprint res
*)

(*
let _ = print_endline @@ "Quelques tests du compilateur, en vrac :"

let ld = Lexing.dummy_pos
let st = Stack.create
let ex_wrap code = exec (st()) (Env.create, "") code (st())

(* opération de base 1 + (4*5) : fonctionne *)
let e3 = BinOp(addOp,Const 1, BinOp(multOp, Const 4, Const 5, ld), Lexing.dummy_pos)
let _ = print_endline @@ ex_wrap (compile e3)

(* opération 10*100 avec affichage de 10 : fonctionne *)
let e4 = BinOp(multOp, Printin(Const 10, ld), Const 100, ld)
let _ = print_endline @@ ex_wrap (compile e4)

let code1 = [C 10; C 15; BOP addOp; LET "x"; ACCESS "x"; C 3; BOP multOp; ENDLET]
let _ = print_endline @@ ex_wrap code1 

(* on applique une CLOSURE dans laquelle env["x"] = 2, et on réalise l'opération 2*x + 1 : fonctionne, renvoie 5 *)
let c = [ACCESS("x"); C 1; BOP addOp; ACCESS("x"); BOP addOp; RETURN] 
let _ = print_endline @@ ex_wrap [CLOSURE("x", c);  C 2; APPLY]

(* on applique une fermeture pour faire "1" + 1 où env["1"] = 2 : fonctionne, renvoie 3 *)
let c = [ACCESS("1"); C 1; BOP addOp; RETURN] 
let _ = print_endline @@ ex_wrap [CLOSURE("1",c); C 2; APPLY]

(* utilisation de la fonction fun x -> x+x sur 3 : fonctionne, renvoie 6 *)
let e4 = In(Fun(Ident("x", ld), BinOp(addOp, Ident("x", ld), Ident("x", ld), ld), ld), Const 3, ld)
let c4 = compile e4
let _ = print_endline @@ ex_wrap c4
*)
exception Error of exn * (int * int * string )
let lexbuf = Lexing.from_channel stdin (*(open_in "test.fo")*)
let parse_buf_exn lexbuf =
    try
      Parser.main Lexer.token lexbuf
    with exn ->
      begin
        let tok = Lexing.lexeme lexbuf in
        raise (send_parsing_error (Lexing.lexeme_start_p lexbuf) tok)
      end

type test = {pos_bol : int; pos_fname : string; pos_lnum : int; pos_cnum : int}



let rec test_compil ()=
    
    let _ = print_string ">> "; flush stdout
    in let parse () = Parser.main Lexer.token lexbuf
    in let r = parse ()
    in let code = compile r 
    in begin
        print_endline @@ print_code code ;
        print_endline @@ exec_wrap code ;
        test_compil ()
       end

type interpretor_params = {
    repl : bool;
    disp_pretty : bool;
    disp_result : bool;
}



let rec readExpr lexbuf env inter_params =
  let r = 
    try
      parse_buf_exn lexbuf
    with ParsingError x ->
      let _ = print_endline x in Unit
  in match r with
  | Open (file, _) -> 
    let file_path = String.sub file 5 (String.length file - 5) 
    in let env' = interpretFromStream (Lexing.from_channel (open_in file_path)) file_path env {inter_params with repl = false} in Unit, env'
  | Eol -> Eol, env
  | _ ->  let _ = if inter_params.disp_pretty then begin print_endline @@ beautyfullprint r;  end else ()
    in let env, type_expr = analyse r env
    in let _ = print_endline @@ print_type type_expr
    in let env'  = begin
        try
          let res, env' = interpret r env (fun x y -> x, y) (fun x y -> x, y)
          in  let _ = if inter_params.disp_result then print_endline @@ beautyfullprint res else ()
          in env'
        with InterpretationError x -> 
          let _ = print_endline x in env
      end in r, env'   

and repl lexbuf env inter_params = 
  let _ = if inter_params.repl then begin  print_string ">> "; flush stdout end else ()
  (*) in let parse () = Parser.main Lexer.token lexbuf
    in let r = parse ()
  *)
  in let expr, env' = readExpr lexbuf env inter_params
  in if expr = Eol then env' else repl lexbuf env' inter_params


and interpretFromStream lexbuf name env inter_params =
  let pos = lexbuf.Lexing.lex_curr_p in
  let pos = {pos_bol = pos.Lexing.pos_cnum; 
             pos_fname = pos.Lexing.pos_fname; 
             pos_lnum = pos.Lexing.pos_lnum;
             pos_cnum = pos.Lexing.pos_cnum;}


  in begin
    lexbuf.lex_curr_p <- {
                          pos_bol = 0;
                          pos_fname = name;
                          pos_lnum = 0;
                          pos_cnum = 0;
                        };
    let env' = repl lexbuf env inter_params in
    lexbuf.lex_curr_p <- {pos_bol = pos.pos_bol;
                         pos_fname = pos.pos_fname;
                         pos_lnum = pos.pos_lnum;
                         pos_cnum = pos.pos_cnum;
                        };
      env'
    end

let mode = "INTERPRETATIO"

(* let _ = repl (Env.create) *)
let _ =     if mode = "INTERPRETATION" then
    interpretFromStream lexbuf "test" (Env.create) {repl = true; disp_pretty = true; disp_result = true;}
      else 
 test_compil ()
(*
let test () = begin
    let a = 4 in let  b = 8 in 4;
    let a = 4 in 8;
    a * 10 + b
end
let _ = print_int (test ())
*) 
