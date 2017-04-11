open Parser
open Expr
open Errors
open Env
open Interpret
open Compil
open Binop
open Inference
open Secd

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


type interpretor_params = {
  repl : bool;
  disp_pretty : bool;
  disp_result : bool;
  use_inference : bool
}
let interpret_repl program env type_expr inter_params =
  try
    let res, env' = interpret program env (fun x y -> x, y) (fun x y -> raise (InterpretationError ("Exception non caught: " ^ beautyfullprint x)); x, y)
    in let type_expr = 
         if inter_params.use_inference then
           type_expr
         else begin match res with
           | Const _ -> Int_type
           | Bool _ -> Bool_type
           | Unit -> Unit_type
           | RefValue _ -> Ref_type (Var_type (get_new_pol_type()))
           | Array _ -> Array_type
           | _ -> Fun_type (Var_type (get_new_pol_type()), Var_type (get_new_pol_type ()))
         end

    in  let _ = if inter_params.disp_result then 
            Printf.printf "- %s : %s\n" (print_type type_expr) (beautyfullprint res)
          else ()
    in env'
  with InterpretationError x -> 
    let _ = print_endline x in env
(*
let compile_repl program env type_expr inter_params =
  let code = compile program
  in begin 
    print_endline @@ print_code code ;
    print_endline @@ exec_wrap code;
    env
    end
*)


let rec extract_line lexbuf acc = 
  let program = parse_buf_exn lexbuf 
  in begin
    match program with
    | Eol ->  true, acc
    | Open (file, _)  -> print_endline file; false, ((get_code file) @ acc)
          (*
        | Open (file, _) -> print_endline file; aux ((convert_file_lines @@ get_code file) @ acc)
             *)
    | x  -> false, x :: acc
  end
and get_code file_name = begin
  let lexbuf = Lexing.from_channel @@ open_in file_name
  in let pos = lexbuf.Lexing.lex_curr_p 
  in let pos = {pos_bol = pos.Lexing.pos_cnum; 
                pos_fname = pos.Lexing.pos_fname; 
                pos_lnum = pos.Lexing.pos_lnum;
                pos_cnum = pos.Lexing.pos_cnum;}

  in let _ = lexbuf.lex_curr_p <- {
      pos_bol = 0;
      pos_fname = file_name;
      pos_lnum = 1;
      pos_cnum = 0;
    }

  in let rec aux acc =  begin
      let reached_eof, l = extract_line lexbuf acc
      in if reached_eof then
        l
      else aux l
    end
  in let code = begin
      try
        aux []
      with ParsingError x ->
        let _ = Lexing.flush_input lexbuf
        in let _ = Parsing.clear_parser ()
        in let _ = print_endline x in []
    end


  in let _ = lexbuf.lex_curr_p <- {pos_bol = pos.pos_bol;
                                   pos_fname = pos.pos_fname;
                                   pos_lnum = pos.pos_lnum;
                                   pos_cnum = pos.pos_cnum;
                                  }
  in code
end

let get_line lexbuf =
  let lines = begin try
      snd @@ extract_line lexbuf []
    with ParsingError x ->
      let _ = Lexing.flush_input lexbuf
      in let _ = Parsing.clear_parser ()
      in let _ = print_endline x in []
  end
  in  if lines = [] then Unit else
    List.fold_left (fun a b -> MainSeq(b, a, Lexing.dummy_pos)) (List.hd lines) (List.tl lines)

let parse_whole_file file_name =
  let lines = get_code file_name 
  in if lines <> [] then
    List.fold_left (fun a b -> MainSeq(b, a, Lexing.dummy_pos)) (List.hd lines) (List.tl lines)
  else Unit


let execute_code code env = 
  let res, env' = interpret code !env (fun x y -> env := y; x, y) (fun x y -> raise (InterpretationError ("Exception non caught: " ^ beautyfullprint x)); x, y)
  in res, env'

       
type parameters_structure = 
  {debug : bool ref;
   use_inference: bool ref;
   machine: bool ref;
   interm : string ref}

let execute_with_parameters code context_work params env =
  let _ = if !(params.debug) then
      print_endline @@ beautyfullprint code
  in let error = ref false
  in let  env', type_expr = 
       if !(params.use_inference)   then
         begin try
             analyse code !env
           with InferenceError (Msg m) ->
             let _ = error := true
             in let _ = print_endline m in !env, Unit_type
         end
       else !env, Unit_type
  in let _ = env := env'
  in 
    if not !error then
      context_work code params type_expr env
    else env

let context_work_machine code params type_expr env =
  let bytecode = compile code
  in  let _ = if  !(params.interm) <> "" then begin
    Printf.fprintf (open_out !(params.interm)) "%s" @@ print_code bytecode 
  end
  in let _ = print_endline @@ exec_wrap bytecode !(params.debug)
  in env


let rec test_compil () debug=

  let _ = print_string ">> "; flush stdout
  in let parse () = Parser.main Lexer.token lexbuf
  in let r = parse ()
  in let code = compile r 
  in begin
      print_endline @@ beautyfullprint r;
      print_endline @@ print_code code ;
    print_endline @@ exec_wrap code debug;
  end


let context_work_interpret code params type_expr env =
  try
    let res, env' = 
      interpret code !env (fun x y -> env := y; x, y) (fun x y -> raise (InterpretationError ("Exception non caught: " ^ beautyfullprint x)); x, y)
    in let type_expr = 
         if !(params.use_inference) then
           type_expr
         else begin match res with
           | Const _ -> Int_type
           | Bool _ -> Bool_type
           | Unit -> Unit_type
           | RefValue _ -> Ref_type (Var_type (get_new_pol_type()))
           | Array _ -> Array_type
           | _ -> Fun_type (Var_type (get_new_pol_type()), Var_type (get_new_pol_type ()))
         end

    in  let _ =  
            Printf.printf "- %s : %s\n" (print_type type_expr) (beautyfullprint res)
    in let _ = env := env'
    in env
  with InterpretationError x -> 
    let _ = print_endline x in env

let execute_file file_name params context_work =
  let code = parse_whole_file file_name in
  execute_with_parameters code context_work params (ref Env.create)

let repl params context_work = 
  let lexbuf = Lexing.from_channel stdin 
  in let rec aux env = 
       let _ = print_string ">> "; flush stdout
       in let code = get_line lexbuf
       in let env = execute_with_parameters code context_work params env
       in aux env
              (*
       in 
       let res, env' = execute_code code env
       in let _ = print_endline @@ beautyfullprint res in aux env
                 *)
  in aux (ref Env.create)
(*
let rec readExpr execute lexbuf env inter_params =
  let error = ref false
  in let program = begin
      try
        parse_buf_exn lexbuf
      with ParsingError x ->
        let _ = error := true
        in let _ = Lexing.flush_input lexbuf
        in let _ = Parsing.clear_parser ()
        in let _ = lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
                                          pos_bol = 0;
                                          pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1;
                                          pos_cnum = 0;
                                        };
        in let _ = print_endline x in Unit
    end 
  in if not !error then
    match program with
    | Open (file, _) -> 
      let file_path = String.sub file 5 (String.length file - 5) 
      in let env' = interpretFromStream execute (Lexing.from_channel (open_in file_path)) file_path env {inter_params with repl = false} in Unit, env'
    | Eol -> Eol, env
    | _ ->  
      let _ = if inter_params.disp_pretty then 
          begin print_endline @@ beautyfullprint program;  end 
        else ()
      in let  env, type_expr = 
           if inter_params.use_inference   then
             begin try
                 analyse program env
               with InferenceError (Msg m) ->
                 let _ = error := true
                 in let _ = print_endline m in env, Unit_type
             end
           else env, Unit_type

      (*      in let _ = print_endline @@ print_type type_expr *)
      in let env'  = 
           if not !error then
             begin
               execute program env type_expr inter_params
                 (*
               try
                 let res, env' = interpret program env (fun x y -> x, y) (fun x y -> raise (InterpretationError ("Exception non caught: " ^ beautyfullprint x)); x, y)
                 in let type_expr = 
                      if inter_params.use_inference then
                        type_expr
                      else begin match res with
                        | Const _ -> Int_type
                        | Bool _ -> Bool_type
                        | Unit -> Unit_type
                        | RefValue _ -> Ref_type (Var_type (get_new_pol_type()))
                        | Array _ -> Array_type
                        | _ -> Fun_type (Var_type (get_new_pol_type()), Var_type (get_new_pol_type ()))
                      end

                 in  let _ = if inter_params.disp_result then 
                         Printf.printf "- %s : %s\n" (print_type type_expr) (beautyfullprint res)
                       else ()
                 in env'
               with InterpretationError x -> 
                 let _ = print_endline x in env
                    *)
             end 
           else env
      in program, env'   
  else 
    Unit, env

(*let rec readExpr lexbuf env inter_params =
  let program = 
    try
      parse_buf_exn lexbuf
    with ParsingError x ->
      let _ = Lexing.flush_input lexbuf
      in let _ = Parsing.clear_parser ()
      in let _ = lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with
                                        pos_bol = 0;
                                        pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1;
                                        pos_cnum = 0;
                                      };
      in let _ = print_endline x in Unit
  in match program with
  | Open (file, _) -> 
    let file_path = String.sub file 5 (String.length file - 5) 
    in let env' = interpretFromStream (Lexing.from_channel (open_in file_path)) file_path env {inter_params with repl = false} in Unit, env'
  | Eol -> Eol, env
  | _ ->  let _ = if inter_params.disp_pretty then begin print_endline @@ beautyfullprint program;  end else ()
    in let  env, type_expr = begin try
           analyse program env
         with InferenceError (Msg m) ->
           let _ = print_endline m in env, Unit_type
       end

    in let _ = print_endline @@ print_type type_expr
    in let env'  = begin
        try
          let res, env' = interpret program env (fun x y -> x, y) (fun x y -> x, y)
          in  let _ = if inter_params.disp_result then print_endline @@ beautyfullprint res else ()
          in env'
        with InterpretationError x -> 
          let _ = print_endline x in env
      end in program, env'   
*)
and repl execute lexbuf env inter_params = 
  let _ = if inter_params.repl then begin  print_string ">> "; flush stdout end else ()
  (* in let parse () = Parser.main Lexer.token lexbuf
     in let r = parse ()
  *)
  in let expr, env' = readExpr execute lexbuf env inter_params
  in if expr = Eol then env' else repl execute lexbuf env' inter_params


and interpretFromStream execute lexbuf name env inter_params =
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
    let env' = repl execute lexbuf env inter_params in
    lexbuf.lex_curr_p <- {pos_bol = pos.pos_bol;
                          pos_fname = pos.pos_fname;
                          pos_lnum = pos.pos_lnum;
                          pos_cnum = pos.pos_cnum;
                         };
    env'
  end
*)
let mode = "INTERPRETATIN"

let _ = print_string @@ Printf.sprintf 
    "___________             .__                 
\\_   _____/____   __ __ |__|  ____    ____  
 |    __) /  _ \\ |  |  \\|  | /    \\ _/ __ \\ 
 |     \\ (  <_> )|  |  /|  ||   |  \\\\  ___/ 
 \\___  /  \\____/ |____/ |__||___|  / \\___  >
     \\/                          \\/      \\/   "

(*
(* let _ = repl (Env.create) *)
let _ =     if mode = "INTERPRETATION" then
    interpretFromStream lexbuf "stdin" (Env.create) {repl = true; disp_pretty = true; disp_result = true; use_inference = true}
      else 
 test_compil ()
   *)

let options_debug = ref false
let options_compile = ref ""
let options_compile_execute = ref false
let options_use_inference = ref false
let options_input_file = ref ""
let options_use_coloration = ref false


let () = 
  let params = {use_inference = ref false;
                debug = ref false;
                machine = ref false;
               interm = ref ""}
  in let speclist = 
    [("-debug", Arg.Set params.debug, "Prettyprint the program" );
     ("-machine", Arg.Set params.machine, "compile and execute the program using a secd machine");
     ("-inference", Arg.Set params.use_inference, "use type inference for more efficience error detection");
     ("-coloration", Arg.Set options_use_coloration, "use syntastic coloration");
     ("-interm", Arg.Set_string options_compile, "output the compiled program to a file")]
  in let source = ref (stdin) 
  in let _ =  begin
      Arg.parse speclist (fun x -> options_input_file := x) "blah blahA";
      (*if !options_input_file <> "" then 
        source := open_in !options_input_file 
        else ();*)
      let context_work = if !(params.machine) then (
          print_endline "Interactive Compiler / SECD";
          context_work_machine) 
        else (
          print_endline "Interpreter";
          context_work_interpret
        )
          
      in if !options_input_file <> ""  then begin
        print_endline !options_input_file;
        execute_file !options_input_file params context_work
      end
      else
      begin
        repl params context_work
      end
    end
  in ()

(*
let test () = begin
    let a = 4 in let  b = 8 in 4;
    let a = 4 in 8;
    a * 10 + b
end
let _ = print_int (test ())
*) 
