open Lexer
open Shared.Env
open Buildins
open Lexing
open Parser
open Expr
open Errors
open Shared
open Interpret
open CompilB
open Bruijn
open Jit
open Binop
open Inference
open SecdB
open Prettyprint
open Transformation_ref
open Transformation_except

(* type for easier parameter passing *)
type parameters_structure =
  {debug                    : bool ref;
   use_inference            : bool ref;
   machine                  : bool ref;
   r                        : bool ref;
   e                        : bool ref;
   interm                   : string ref;
   out_pretty_print         : string ref;
   out_file                 : out_channel ref
  }

let transform_buildin_type t params =
  let t = if !(params.e) then transform_exceptions_type t else t
  in let t = if !(params.r) then transform_ref_type t else t
  in t


let transform_buildin buildin params =
  if !(params.e) && !(params.r) then transform_buildin_all buildin 
  else if !(params.e) then transform_buildin_exceptions buildin
  else if !(params.r) then transform_buildin_ref buildin
  else buildin
(*let buildin = if !(params.e) then transform_buildin_exceptions buildin else buildin
  in let buildin = if !(params.r) then transform_buildin_ref buildin else buildin
  in*) 



let make_lib params =
  let meta = fun x -> transform_buildin (FBuildin x) params 
  in let meta_type = fun x -> transform_buildin_type x params 

  in let make_arithm_binop symbol  fct = 
       (symbol,
        meta_type @@ Fun_type(Int_type, Fun_type(Int_type, Int_type)),
        (
          meta @@ fun x -> meta @@ fun y -> match (x, y) with | FInt a, FInt b -> FInt (fct a b) | _ -> raise (send_error "ousp" Lexing.dummy_pos)
        ), 

        Bclosure(fun a -> Dream.DreamEnv.BUILTCLS(fun b -> 
            match (a, b) with 
            | Dream.DreamEnv.CST a, Dream.DreamEnv.CST b -> Dream.DreamEnv.CST (fct a b) 
            | _ -> raise (send_error "ousp" Lexing.dummy_pos)))
       ) 
  in let make_ineg_binop symbol  fct fctm = 
       (symbol, (
           let new_type = Generic_type (new_generic_id ())
           in meta_type @@ Fun_type(new_type, Fun_type(new_type, Bool_type))),
        (meta @@ fun x -> meta @@ fun y -> FBool(fct x y)
        ) , 
        Bclosure(fun a -> Dream.DreamEnv.BUILTCLS(fun b -> Dream.DreamEnv.CST (int_of_bool @@ fctm a b)))
       ) 
  in let make_bincomp_binop symbol  fct = 
       (symbol, 
        meta_type @@ Fun_type(Bool_type, Fun_type(Bool_type, Bool_type)),
        (meta @@ fun x -> meta @@ fun y -> match (x, y) with | FBool a, FBool b -> FBool (fct a b) | _ -> raise (send_error "ousp" Lexing.dummy_pos)
        ) , 
        Bclosure(fun a -> Dream.DreamEnv.BUILTCLS(fun b -> 
            match a, b with
            | Dream.DreamEnv.CST a, Dream.DreamEnv.CST b ->         
              Dream.DreamEnv.CST (int_of_bool @@ fct (bool_of_int a) (bool_of_int b))
            | _ -> raise (send_error "ousp" Lexing.dummy_pos)

          ))
       ) 


  in  [
    make_arithm_binop    "+"    (+);
    make_arithm_binop    "*"    ( * );
    make_arithm_binop    "-"    (-);
    make_arithm_binop    "/"    (/);
    make_bincomp_binop   "&&"   (&&);
    make_bincomp_binop   "||"   (||);
    make_ineg_binop      "="    Shared.ast_equal          Dream.DreamEnv.dream_item_equal;
    make_ineg_binop      "<>"   Shared.ast_nequal         Dream.DreamEnv.dream_item_nequal;
    make_ineg_binop      ">="   Shared.ast_glt_or_equal   Dream.DreamEnv.dream_item_glt_or_equal;
    make_ineg_binop      ">"    Shared.ast_glt            Dream.DreamEnv.dream_item_glt;
    make_ineg_binop      "<="   Shared.ast_slt_or_equal   Dream.DreamEnv.dream_item_slt_or_equal;
    make_ineg_binop      "<"    Shared.ast_slt            Dream.DreamEnv.dream_item_slt;

    ("buildins_plus_id",
     Fun_type(Int_type, Fun_type(Int_type, Int_type)),
     (FBuildin (fun x -> FBuildin(fun y -> 
          match x, y with 
          | FInt x, FInt y -> FInt (x+y)
          | _ -> raise (send_error "ouspi" Lexing.dummy_pos)
        ))
     ), Const 4

    );
    ("buildins_eq_id",
     (let g = Generic_type (new_generic_id () )
      in Fun_type(g, Fun_type(g, Bool_type))),
     (FBuildin (fun x -> FBuildin(fun y -> FBool(Shared.ast_equal x y)
        ))
     ), Const 4);

    ("prInt", 
     meta_type @@ Fun_type(Int_type, Int_type), 
     (meta @@
      fun x -> 
      match x with 
      | FInt x -> print_string "yezosthi";print_int x; print_endline ""; FInt x 
      | _ -> raise (send_error "print prends un argument un entier" Lexing.dummy_pos)
     ),
     (Bclosure(fun a ->
          match a with
          | Dream.DreamEnv.CST a -> let _ = print_endline @@ "yes "^string_of_int a in Dream.DreamEnv.CST a
          | _ -> raise (send_error "print prends un argument un entier" Lexing.dummy_pos)
        ))

    );
    ("aMake", 
     meta_type @@ Fun_type(Int_type, Array_type Int_type),
     (meta @@ fun x -> 
      match x with
      | FInt x when x >= 0 -> FArray (Array.make x 0)
      | _ -> raise (send_error "aMake only takes positive integer as parameter" Lexing.dummy_pos)
     ), 
     (Bclosure(fun a ->
          match a with
          | Dream.DreamEnv.CST a ->   Dream.DreamEnv.ARR (Array.make a 0)
          | _ -> raise (send_error "aMake only takes positive integer as parameter" Lexing.dummy_pos)
        ))
    );
    ("not",
     meta_type @@ Fun_type(Bool_type, Bool_type),
     (meta @@ fun x -> match x with | FBool b -> FBool (not b)
                                    | _ -> raise (send_error "not prends un argument bool" Lexing.dummy_pos)
     ), 
     (Bclosure(fun a -> 
          match a with
          | Dream.DreamEnv.CST 0 -> Dream.DreamEnv.CST 1
          | Dream.DreamEnv.CST _ -> Dream.DreamEnv.CST 0
          | _ -> raise (send_error "not prends un argument bool" Lexing.dummy_pos)
        ))
    );
  ]
(* parse a lexbuf, and return a more explicit error when it fails *)
let parse_buf_exn lexbuf params =
  try
    Parser.main Lexer.token (*(if !(params.machine) && (!(params.e) || !(params.r)) then 
                              let _ = print_endline "loading thing" in let _ = Shared.buildins_activated := false in Lexer_machine.token 
                              else let _ = Shared.buildins_activated := true in Lexer.token)*) lexbuf
  with exn ->
    begin
      let tok = Lexing.lexeme lexbuf in
      raise (send_parsing_error (Lexing.lexeme_start_p lexbuf) tok)
    end


(* extract a line from a lexbuf . Load file when necessary *)
let rec extract_line lexbuf acc params = 
  let program = parse_buf_exn lexbuf params
  in begin
    match program with
    | Eol ->  true, acc
    | Open (file, _)  -> false, ((get_code file params) @ acc)
    | x  -> false, x :: acc
  end
(* get all the code contained in the file name (it parse until reaching a eol). 
   It also deals with saving/setting informations for debugging 
   It also check for parsing error
   Return a list of lines
*)
and get_code file_name params = begin
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
        let reached_eof, l = extract_line lexbuf acc params
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
let parse_line lexbuf params =
  let lines = begin try
      snd @@ extract_line lexbuf [] params
    with ParsingError x ->
      let _ = Lexing.flush_input lexbuf
      in let _ = Parsing.clear_parser ()
      in let _ = print_endline x in []
  end
  in  if lines = [] then [Unit] else
    List.rev lines
(*  [List.fold_left (fun a b -> MainSeq(b, a, Lexing.dummy_pos)) (List.hd lines) (List.tl lines)]*)

(* return an expr representing all the code in a file *)
let parse_whole_file file_name params =
  let lines = get_code file_name  params
  in if lines <> [] then
    (*[List.fold_left (fun a b -> MainSeq(b, a, Lexing.dummy_pos)) (List.hd lines) (List.tl lines)]*)
    List.rev lines
  else [Unit]

let std_lib_machine = 
  let p = Lexing.dummy_pos in
  let id n = Ident(([], n), p) in

  [(*
   ("buildins_y",
    (let a = Generic_type (new_generic_id ()) in let b = Generic_type (new_generic_id ()) in
    Fun_type(Fun_type(Fun_type(Fun_type(Fun_type(a, b), a), b), a), b)),

    Fun(id "t",
        In(Let(id "p", 
            Fun(id "f", Fun(id "x", Call(Call(id "t", Call(id "f", id "f", p), p), id "x", p), p), p), p), Call(id "p", id "p", p), p), p)
   )*)
    (*("+.",
      Fun_type(Int_type, Fun_type(Int_type, Int_type)),
      Bclosure(fun (Dream.DreamEnv.CST a) -> Dream.DreamEnv.BUILTCLS(fun (CST b) -> CST (a+b)))
      );*)
  ] 

let load_std_lib_machine code params =
  let p = Lexing.dummy_pos in
  let lib = make_lib params in
  List.fold_left (fun a (id, _, _, fct) -> MainSeq(Let(Ident(([], id), p), fct, p), a, p)) code lib
(*)
  MainSeq(Let(Ident(([], "hello"), p), Bclosure(fun (Dream.DreamEnv.CST a) -> Dream.DreamEnv.BUILTCLS (fun (CST b) -> CST (a+b))), p), code, p)
*)
let load_std_lib_machine_types env params =
  let p = Lexing.dummy_pos in
  let lib = make_lib params in
  List.fold_left (fun a (id, ty, _, _) -> Env.add_type a ([], id) ty) env lib




let rec compare_type_to_model model t =
  match (model, t) with
    | Int_type, Int_type
    | Bool_type, Bool_type
    | Unit_type, Unit_type ->
      true

    | Polymorphic_type a, Polymorphic_type b -> a = b 
    | Called_type (name, _, l), Called_type(name', _, l') ->
      name = name' && List.length l = List.length l'


    | Generic_type a, Generic_type b -> a = b
  | Ref_type a, Ref_type b 
  | Array_type a, Array_type b -> 
    compare_type_to_model a b
  | _, _ -> false 

let compare_to_signature signature path =
  false






(* execute some code in a given environment. Take into account the params `params` 
   context_work his a function which will execute the code *)
let rec execute_with_parameters_line base_code context_work params env =
  let code = base_code
  in let env =
    match code with
    | Module (name, lines, sg, _) ->
      let env = Env.create_module env name
      in let env = Env.enter_module env name
      in let env = List.fold_left (fun e l -> execute_with_parameters_line l context_work params e) env lines
      in let env = Env.quit_module env name
      in let _ = match sg with
          | None -> ()
          | Some (Register x ) -> ()
          | Some (Unregister l) ->
            ()
      in env
    | _ -> env
  in
  let code = if !(params.e) then
      let _ = print_endline "=##################}" in
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
  in let rec inference_analyse code env =
       if !(params.use_inference)   then
         begin try
             let env = if !(params.machine) then load_std_lib_machine_types env params else env in
             Inference.analyse code env
           with 
            | InferenceError (Msg m) | InferenceError (UnificationError m)->
             let _ = error := true
             (* print on both stderr and stdout *)
             in let _ = Printf.fprintf stderr "%s\n" m in let _ = flush stderr
             in env, Unit_type
             (*    in let _ = Printf.printf "%s\n" m in env, Unit_type*)
            | LoadModule (name, path) ->
              let _ = print_endline "LOAD NEW MODULE" in
              let module_code = parse_whole_file path  params in
              let env = execute_with_parameters_line (Module(name, module_code, None, Lexing.dummy_pos)) context_work params env
              in inference_analyse code env
         end
       else env, Unit_type
  in let  env', type_expr =  inference_analyse code env

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
  let code = load_std_lib_machine code params in
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
let rec context_work_interpret code params type_expr env =
  try
    let res, env' = 
      let rec loop_interpret code env =
        begin try
              Interpret.interpret code env  k kE 
          with 
          | LoadModule (name, path) ->
              let _ = print_endline "LOAD NEW MODULE" in
              let module_code = parse_whole_file path  params in
              let env = execute_with_parameters_line (Module(name, module_code, None, Lexing.dummy_pos)) context_work_interpret params env
              in loop_interpret code env
        end
      in loop_interpret code env
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
  let code = parse_whole_file file_name  params in
  execute_with_parameters code context_work params env

let load_buildins_fix env params =
  execute_file "buildins/fix.ml" params context_work_interpret env

let load_buildins_ref env params =
  execute_file "buildins/ref.ml" {params with r = ref false; e = ref false


                                 } context_work_interpret env

let load_from_var var env context_work params = 
  execute_with_parameters (parse_line (Lexing.from_string var) params ) context_work params env


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
  let lib = make_lib params in
  let rec aux env l = match l with
    | [] -> env
    | (name, fct_type, fct, _)::tl ->
      let name = ([], name) in
      let env = Env.add env name fct
      in let env = Env.add_type env name (fct_type)
      in aux env tl
  in let env = aux env lib
  in
  let env = load_from_var list_type_declaration env context_work {params with r = ref false; e = ref false}
  in let env = load_from_var buildins_create env context_work {params with r = ref false; e = ref false}
  in let env = load_from_var create_repl_ref env context_work {params with r = ref false; e = ref false}

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
       in let code = parse_line lexbuf params
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
  let params = {use_inference = ref true;
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
        ("-noinference", Arg.Set params.use_inference, "disable type inference");
        ("-nocoloration", Arg.Clear Format.color_enabled, "use syntastic coloration");
        ("-o", Arg.Set_string params.out_pretty_print, "choose a file where to write the code evaluated");
        ("-nobuildins", Arg.Clear Shared.buildins_activated, "disable buildins");
        ("-interm", Arg.Set_string params.interm, "output the compiled program to a file")]
  in let _ =  begin
      Arg.parse speclist (fun x -> options_input_file := x) "Fouine interpreter / compiler";
      if !(params.machine) && (!(params.e) || !(params.r)) then
        Shared.buildins_activated := false
      else ();
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
        ignore @@ execute_file !options_input_file params context_work (if !(params.machine) then Env.create else load_std_lib (Env.create) context_work params)
      end
      else
        begin
          repl params context_work
        end
    end;
      flush !(params.out_file);
      close_out !(params.out_file)
  in ()

