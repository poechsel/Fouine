open Lexer
open Parser
open Expr
open Errors
open Env
open Interpret
open Compil
open Binop
open Inference
open Secd
open Prettyprint


(* type cloning the structure of the informations the Lexer has about tokens *)
type debug_infos_file = 
  { pos_bol : int;
    pos_fname : string;
    pos_cnum : int;
    pos_lnum: int}
(* type for easier parameter passing *)
type parameters_structure = 
  {debug : bool ref;
   use_inference: bool ref;
   machine: bool ref;
   interm : string ref}


(* parse a lexbuf, and return a more explicit error when it fails *)
let parse_buf_exn lexbuf =
  try
    Parser.main Lexer.token lexbuf
  with exn ->
    begin
      let tok = Lexing.lexeme lexbuf in
      raise (send_parsing_error (Lexing.lexeme_start_p lexbuf) tok)
    end





(* extract a line from a lexbuf . Load file when necessary *)
let rec extract_line lexbuf acc = 
  let program = parse_buf_exn lexbuf 
  in begin
    match program with
    | Eol ->  true, acc
    | Open (file, _)  -> false, ((get_code file) @ acc)
    | x  -> false, x :: acc
  end
(* get all the code contained in the file name (it parse until reaching a eol). 
   It also deals with saving/setting informations for debugging 
   It also check for parsing error
   Return a list of lines
*)
and get_code file_name = begin
  try
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
  with Sys_error (x) -> (
      print_endline x;
      [Unit]
    )
end

(* get a line from a lexbuf, treat parsing errors if some are detected.*)
let parse_line lexbuf =
  let lines = begin try
      snd @@ extract_line lexbuf []
    with ParsingError x ->
      let _ = Lexing.flush_input lexbuf
      in let _ = Parsing.clear_parser ()
      in let _ = print_endline x in []
  end
  in  if lines = [] then Unit else
    List.fold_left (fun a b -> MainSeq(b, a, Lexing.dummy_pos)) (List.hd lines) (List.tl lines)

(* return an expr representing all the code in a file *)
let parse_whole_file file_name =
  let lines = get_code file_name 
  in if lines <> [] then
    List.fold_left (fun a b -> MainSeq(b, a, Lexing.dummy_pos)) (List.hd lines) (List.tl lines)
  else Unit



(* execute some code in a given environment. Take into account the params `params` 
   context_work his a function which will execute the code *)
let execute_with_parameters code context_work params env =
  let _ = if !(params.debug) then
      print_endline @@ pretty_print code
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
  in let _ = if !(params.interm) <> "" then 
         Printf.fprintf (open_out !(params.interm)) "%s" @@ print_code @@ compile code
  in if not !error then
    context_work code params type_expr env
  else env


(* executing code with the secd machine.
   First compile the code, then print it if needed, and finally
   execute the bytecode on the stack machine *)
let context_work_machine code params type_expr env =
  let bytecode = compile code
  in let _ = print_endline @@ exec_wrap bytecode !(params.debug)
  in env


(* interpret the code. If we don't support interference, will give a minimum type inference based on the returned object. 
   Treat errors when they occur *)
let context_work_interpret code params type_expr env =
  try
    let res, env' = 
      interpret code !env (fun x y -> env := y; x, y) (fun x y -> raise (InterpretationError ("Exception non caught: " ^ pretty_print x)); x, y)
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
          Printf.printf "- %s : %s\n" (print_type type_expr) (pretty_print res)
    in let _ = env := env'
    in env
  with InterpretationError x -> 
    let _ = print_endline x in env


(* execute the code in a file *)
let execute_file file_name params context_work =
  let code = parse_whole_file file_name in
  execute_with_parameters code context_work params (ref Env.create)

(* basic repl, very good way to test stuff *)
let repl params context_work = 
  let lexbuf = Lexing.from_channel stdin 
  in let rec aux env = 
       let _ = print_string ">> "; flush stdout
       in let code = parse_line lexbuf
       in let env = execute_with_parameters code context_work params env
       in aux env
  in aux (ref Env.create)



(* because leet hard is just a way to show off *)
let header =  
  "___________             .__                 
\\_   _____/____   __ __ |__|  ____    ____  
 |    __) /  _ \\ |  |  \\|  | /    \\ _/ __ \\ 
 |     \\ (  <_> )|  |  /|  ||   |  \\\\  ___/ 
 \\___  /  \\____/ |____/ |__||___|  / \\___  >
     \\/                          \\/      \\/   "


let options_input_file = ref ""


let () = 
  let params = {use_inference = ref false;
                debug = ref false;
                machine = ref false;
                interm = ref ""}
  in let speclist = 
       [("-debug", Arg.Set params.debug, "Prettyprint the program" );
        ("-machine", Arg.Set params.machine, "compile and execute the program using a secd machine");
        ("-inference", Arg.Set params.use_inference, "use type inference for more efficience error detection");
        ("-coloration", Arg.Set Format.color_enabled, "use syntastic coloration");
        ("-interm", Arg.Set_string params.interm, "output the compiled program to a file")]
  in let _ =  begin
      Arg.parse speclist (fun x -> options_input_file := x) "Fouine interpreter / compiler";
      let context_work = if !(params.machine) then (
          if !options_input_file = "" then print_endline @@ header ^  "Interactive Compiler / SECD";
          context_work_machine) 
        else (
          if !options_input_file = "" then print_endline @@ header ^ "Interpreter";
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
