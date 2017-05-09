open Lexer
open Buildins
open Lexing
open Parser
open Expr
open Errors
open Shared
open Interpret
open CompilB
open Bruijn
open Binop
open Inference
open SecdB
open Prettyprint
open Transformation_ref
open Transformation_except

(* type for easier parameter passing *)
type parameters_structure = 
  {debug : bool ref;
   use_inference: bool ref;
   machine: bool ref;
   r: bool ref;
   e: bool ref;
   interm : string ref;
   out_pretty_print : string ref;
   out_file : out_channel ref
  }


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
  in  if lines = [] then [Unit] else
    List.rev lines
(*  [List.fold_left (fun a b -> MainSeq(b, a, Lexing.dummy_pos)) (List.hd lines) (List.tl lines)]*)

(* return an expr representing all the code in a file *)
let parse_whole_file file_name =
  let lines = get_code file_name 
  in if lines <> [] then
    (*[List.fold_left (fun a b -> MainSeq(b, a, Lexing.dummy_pos)) (List.hd lines) (List.tl lines)]*)
    List.rev lines
  else [Unit]



(* execute some code in a given environment. Take into account the params `params` 
   context_work his a function which will execute the code *)
let rec execute_with_parameters_line code context_work params env =
  let env =
    match code with
    | Module (name, lines, _) ->
      let env = Env.create_module env name
      in let env = Env.enter_module env name
      in let env = List.fold_left (fun e l -> execute_with_parameters_line l context_work params e) env lines
      in Env.quit_module env name
    | _ -> env
  in
  let code = if !(params.e) then
      transform_exceptions code
    else code
  in 
  let code = if !(params.r) then
      transform_ref code
    else code
  in
  let _ = if !(params.debug) then
      print_endline @@ pretty_print @@ code
  in let _ = if (!(params.out_pretty_print) <> "") then
         let previous = !(Format.color_enabled)
         in let _ = Format.color_enabled := false 
         in let _ = output_string !(params.out_file) @@ (pretty_print @@ code) ^ "\n\n"
         in let _ = Format.color_enabled := previous 
        in flush !(params.out_file);

  in let error = ref false
  in let  env', type_expr = 
       if !(params.use_inference)   then
         begin try
             analyse code env
           with InferenceError (Msg m) | InferenceError (UnificationError m)->
             let _ = error := true
             (* print on both stderr and stdout *)
             in let _ = Printf.fprintf stderr "%s\n" m in let _ = flush stderr
             in env, Unit_type
             (*    in let _ = Printf.printf "%s\n" m in env, Unit_type*)
         end
       else env, Unit_type

  (* in let _ = if !(params.interm) <> "" then 
          Printf.fprintf (open_out !(params.interm)) "%s" @@ print_code @@ compile @@ convert code
  *) in if not !error then
    context_work (code) params type_expr env'
  else env'

let execute_with_parameters code_lines context_work params env =
  (*let _ = List.iter (fun x -> print_endline @@ pretty_print x) code_lines
    in*)  if !(params.machine) then
    let code_lines = List.rev code_lines in
    execute_with_parameters_line (List.fold_left (fun a b -> MainSeq (b, a ,Lexing.dummy_pos)) (List.hd code_lines) (List.tl code_lines)) context_work params env
  else 
    let rec aux env l = match l with
      | [] -> env
      | x::tl -> aux (execute_with_parameters_line x context_work params env) tl
    in aux env code_lines


(* executing code with the secd machine.
   First compile the code, then print it if needed, and finally
   execute the bytecode on the stack machine *)
let context_work_machine code params type_expr env =
  let bytecode = compile (convert_bruijn code !(params.debug))
  in let _ = if !(params.interm) <> "" then 
          Printf.fprintf (open_out !(params.interm)) "%s" @@ print_code bytecode true
  in let _ = begin
      if !(params.debug) then begin
        print_endline "\nFull bytecode:";
        print_endline @@ "--" ^ (print_code bytecode true);
        print_endline "" end;
      if bytecode <> [] then 
        print_endline @@ exec_wrap bytecode {debug = ref !(params.debug); nb_op = ref 0; t = Unix.gettimeofday ()} end
  in env

let k : (fouine_values -> fouine_values Env.t -> fouine_values * fouine_values Env.t) = fun x y -> x, y
let kE : (fouine_values -> fouine_values Env.t -> (fouine_values * fouine_values Env.t)) = fun x y -> begin 
    let _ = ignore @@ raise (InterpretationError ("Exception non caught: " ^ print_value x)) in
    (x, y)
  end

let get_default_type expr =
  match expr with
  | FInt _ -> Int_type
  | FBool _ -> Bool_type
  | FUnit -> Unit_type
  | FRef _ -> Ref_type (Generic_type (new_generic_id ()))
  | FArray _ -> Array_type (Generic_type (new_generic_id ()))
  | _ -> Fun_type (Generic_type (new_generic_id ()), Generic_type (new_generic_id ()))


(* interpret the code. If we don't support interference, will give a minimum type inference based on the returned object. 
   Treat errors when they occur *)
let context_work_interpret code params type_expr env =
  try
    let res, env' = 
      interpret code env  k kE 
    in let type_expr = 
         if !(params.use_inference) then
           type_expr
         else 
           get_default_type res
    in  let _ =  
          begin
            let _ = match code with
              | Let (pattern, _, _) 
              | LetRec (pattern, _, _) when !(params.use_inference)->
                let ids = get_all_ids pattern
                in List.iter (fun x -> 
                    let ty = Env.get_type env' x in 
                               Printf.printf "- var %s: %s = %s\n" (string_of_ident x) (print_type ty)
                                 (
                                  print_value (Env.get_most_recent env' x)
                                 )
                             ) ids
              | Let (pattern, _, _) 
              | LetRec (pattern, _, _)->
                let ids = get_all_ids pattern
                in List.iter (fun x -> 
                    let ty =  get_default_type @@ Env.get_most_recent env' x in
                               Printf.printf "- var %s: %s = %s\n" (string_of_ident x) 
                                 (print_type ty)
                                 (
                                  print_value (Env.get_most_recent env' x)
                                 )
                             ) ids

              | _ -> Printf.printf "- %s : %s\n" (print_type type_expr) (print_value res)
            in ();
          end
    in env'
  with InterpretationError x -> 
    let _ = Printf.fprintf stderr "%s\n" x 
    in let _ = flush stderr
    in env
(* in let _ = print_endline x in env*)


(* execute the code in a file *)
let rec execute_file file_name params context_work env=
  let code = parse_whole_file file_name in
  execute_with_parameters code context_work params env

let load_buildins_fix env params =
  execute_file "buildins/fix.ml" params context_work_interpret env

let load_buildins_ref env params =
  execute_file "buildins/ref.ml" {params with r = ref false; e = ref false


                                 } context_work_interpret env

let load_from_var var env context_work params = 
  execute_with_parameters (parse_line (Lexing.from_string var)) context_work params env

let  load_std_lib env context_work params =
  (* La partie commenté concerne les fonctions buildins *)

  (*let p = Lexing.dummy_pos in *)
  (* transformation par continuations des buildins *)
  (*let meta_constructor fct =   BuildinClosure (fun x ->  Closure(Ident("te_k", p), Fun(Ident("te_kE", p),Call(Ident("te_k", p),fct x ,p),p), Env.create)   )  *)
    (* en dessous, transformation pour les refs des continuations *)
  (*meta_constructor fct = (BuildinClosure(fun x e -> Closure(Ident("x", Lexing.dummy_pos), Tuple([fct x e; Ident("x", Lexing.dummy_pos)], Lexing.dummy_pos), Env.create)))
  in
    *)
  (* fonctions "buildins" -> on ne les utilises pas encore *)
  (*let lib = [
    ("prInt", 

     transform_exceptions_type @@ Fun_type(Int_type, Int_type), 
     fun x -> 
       match x with 
       | Const x -> print_int x; print_endline ""; Const x 
       | _ -> raise (send_error "print prends un argument un entier" Lexing.dummy_pos));
    ("aMake", 
     transform_exceptions_type @@ Fun_type(Int_type, Array_type Int_type),
     fun x -> 
       match x with
       | Const x when x >= 0 -> Array (Array.make x 0)
       | _ -> raise (send_error "aMake only takes positive integer as parameter" Lexing.dummy_pos)
    );
    ("ref",
     (let t = Generic_type (new_generic_id ()) in Fun_type(t, Ref_type t)),
     fun x -> RefValue (ref x)
    );
   (* ("testdeux", 
     transform_exceptions_type @@ Fun_type(Int_type, Fun_type(Int_type, Int_type)), 
     fun x ->
       meta_constructor ( 
         fun y ->
           match (x, y) with
           | Const x, Const y -> Const (x+y)
           | _ -> raise (send_error "ouspi" Lexing.dummy_pos)
       ))
     *)
  ]
    in*) 
  let env = load_from_var list_type_declaration env context_work {params with r = ref false; e = ref false}
  in let env = load_from_var buildins_create env context_work {params with r = ref false; e = ref false}
  in let env = load_from_var create_repl_ref env context_work {params with r = ref false; e = ref false}

  (*in let rec aux env l = match l with
      | [] -> env
      | (name, fct_type, fct)::tl ->
        let env = Env.add env name (meta_constructor fct);
        in let env = Env.add_type env name (fct_type)
        in aux env tl
  in let env = aux env lib*)
  in let env = List.fold_left (fun a b -> load_from_var b a context_work params) env buildins_fix
  in let env = List.fold_left (fun a b -> load_from_var b a context_work {params with r = ref false; e = ref false}) env buildins_ref 
  in let env = load_from_var  list_concat env context_work params
  in
  env



(* basic repl, very good way to test stuff *)
let repl params context_work = 
  let lexbuf = Lexing.from_channel stdin 
  in let rec aux env = 
       let _ = print_string ">> "; flush stdout
       in let code = parse_line lexbuf
       in let env = execute_with_parameters code context_work params env
       in aux env
  in let env = Env.create
  in let env = if !(params.machine) then env else load_std_lib env context_work params
  in aux (env)


(* because leet hard is just a way to show off *)
let header =  
  "___________             .__                 
\\_   _____/____   __ __ |__|  ____    ____  
 |    __) /  _ \\ |  |  \\|  | /    \\ _/ __ \\ 
 |     \\ (  <_> )|  |  /|  ||   |  \\\\  ___/ 
 \\___  /  \\____/ |____/ |__||___|  / \\___  >
     \\/                          \\/      \\/   "


let options_input_file = ref ""
let lexbuf = Lexing.from_channel stdin

let () = 
  let params = {use_inference = ref false;
                debug = ref false;
                machine = ref false;
                r = ref false;
                e = ref false;
                out_pretty_print = ref "";
                interm = ref "";
                out_file = ref (open_out "/dev/null")
               }
  in let _ = Format.color_enabled := true
  in let speclist = 
       [("-debug", Arg.Set params.debug, "Prettyprint the program" );
        ("-machine", Arg.Set params.machine, "compile and execute the program using a secd machine");
        ("-ER", Arg.Tuple [Arg.Set params.r; Arg.Set params.e], "apply the refs transformation");
        ("-R", Arg.Set params.r, "apply the refs transformation");
        ("-E", Arg.Set params.e, "apply the exceptions transformation");
        ("-inference", Arg.Set params.use_inference, "use type inference for more efficience error detection");
        ("-nocoloration", Arg.Clear Format.color_enabled, "use syntastic coloration");
        ("-o", Arg.Set_string params.out_pretty_print, "choose a file where to write the code evaluated");
        ("-interm", Arg.Set_string params.interm, "output the compiled program to a file")]
  in let _ =  begin
      Arg.parse speclist (fun x -> options_input_file := x) "Fouine interpreter / compiler";
      if !(params.out_pretty_print) <> "" then
        params.out_file := open_out !(params.out_pretty_print)
      else ();
      let context_work = if !(params.machine) then (
          if !options_input_file = "" then print_endline @@ header ^  "Interactive Compiler / SECD";
          context_work_machine) 
        else (
          if !options_input_file = "" then print_endline @@ header ^ "Interpreter";
          context_work_interpret
        )

      in if !options_input_file <> ""  then begin
        print_endline !options_input_file;
        ignore @@ execute_file !options_input_file params context_work (load_std_lib (Env.create) context_work params)
      end
      else
        begin
          repl params context_work
        end
    end;
      flush !(params.out_file);
      close_out !(params.out_file)
  in ()

