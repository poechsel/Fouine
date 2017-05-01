open Env
open Expr
open CompilB
open Binop
open Stack
open Dream
open Isa
open DreamEnv

type exec_info_structure =
  {debug : bool ref;
   nb_op : int ref}

let incr_exec exec_info = 
  let _ = incr exec_info.nb_op in exec_info

(*
type env_items = CST of int 
               | CLS of string*code*((env_items, type_listing) Env.t)
               | EnvUNITCLS of code*((env_items, type_listing) Env.t)
               | EnvREF of int ref
               | EnvARR of int array 
               | EnvCODE of code
*)
(*
type items = CODE of code 
                | CLS of code * DreamEnv.dream
                | CLSREC of code * DreamEnv.dream
                | BUILTCLS of (instr -> instr)
               (* | UNITCLS of code*(env_items, type_listing) Env.t *)
                | CST of int 
                | REF of int ref
                | ARR of int array
                | ENV of DreamEnv.dream
*)
let print_stack s =
    try
    let v = top s in
    "top of stack -> " ^ 
    begin
      match v with
      | CODE c -> Printf.sprintf "lines of code : %s" (print_code c)
      | CLS (c, e) -> Printf.sprintf "CLOSURE of code %s " (print_code c)
      | CLSREC (c, e) -> Printf.sprintf "CLSREC of some code, some env"
      | CST k -> Printf.sprintf "CST of %s" (string_of_int k)
      | REF r -> Printf.sprintf "REF of value : %s" (string_of_int !r)
      | ARR a -> Printf.sprintf "array "
      | _ -> ""
    end
    with Stack.Empty -> Printf.sprintf "stack is empty for the moment"


(* dans ma stack il y a :
*  - du code (instr list)
*  - des closures (e * code)
*  - des constantes *)
(* i'm now using dump to store old env during LET / ENDLET operations *)

(*
let  o =
    match o with
    | DreamEnv.CST k -> CST k
    | CLS (c, e) -> CLS (c, e)
    | CLSREC (c, e) -> CLSREC (c, e)
    | EnvREF r -> REF r
    | EnvARR a -> ARR a 
    | _ -> failwith "wrong conversion" *)
(*    | CLS (x, c, e) -> CLS (x, c, e) *)

(*
let g o =
    match o with 
    | CST k -> DreamEnv.CST k
    | REF r -> DreamEnv.EnvREF r
    | CLS (c, e) -> DreamEnv.CLS (c, e)
    | CLSREC (c, e) -> DreamEnv.CLSREC (c, e)
    | BUILTCLS f -> EnvBCLS f
    | ARR a -> EnvARR a
    | ENV _ -> failwith "env"
    (* |UNITCLS (c, e) -> EnvUNITCLS (c, e)
    | REF r -> EnvREF r
    *)| _ -> failwith "WRONG_CONVERSION_ENV_FROM_STACK"
*)

exception EXIT_INSTRUCTION
exception RUNTIME_ERROR

let rec exec s e code exec_info =
  match code with 
  | [] -> Printf.sprintf "- : %s" 
                              begin
                              try
                              (let v = pop s
                               in begin 
                                    match v with 
                                    | CST k -> string_of_int k
                                    | (CLS (c, e) | CLSREC (c, e)) -> print_code c
                                    | _ -> "element from stack not printable"
                                  end)
                              with _ ->
                                begin
                                try
                               (let v = DreamEnv.front e in 
                                begin 
                                  match v with 
                                    | CST k -> string_of_int k
                                    | (CLS (c, _) | CLSREC (c, _)) -> print_code c
                                    | _ -> "element from env not printable"
                                end)
                                with _ -> ""
                                end
                              end
  | instr::c ->

    begin
      
      if !(exec_info.debug) then 
      begin
        print_endline @@ Printf.sprintf "\n%s-th instruction" (string_of_int !(exec_info.nb_op));
        print_endline @@ Printf.sprintf "env size : %s" (string_of_int @@ size e);
        print_endline @@ Printf.sprintf "items of the env %s" (DreamEnv.print_env e);
        print_endline @@ Printf.sprintf "next instructions : %s" (print_code c);
        print_endline @@ print_stack s;
        print_endline @@ Printf.sprintf "stack size : %s" (string_of_int @@ length s);
        print_endline @@ print_instr instr 
      end;
    
    match instr with

    | C k -> 
        begin
          push (CST k) s; 
          exec s e c ((incr_exec exec_info))
        end
        
    | REF -> 
        let v = pop s in
        begin
          match v with
          | CST k ->
              begin
                push (REF (ref k)) s; 
                exec s (e) c (incr_exec exec_info)
              end
          | (CLS _ | CLSREC _) -> failwith "ref fun not implemented"
          | _ -> raise RUNTIME_ERROR
        end

    | BANG ->
        let v = pop s in
        begin 
        match v with
        | REF k -> 
            begin 
              push (CST !k) s; 
              exec s (e) c (incr_exec exec_info)
            end
        | _ -> raise RUNTIME_ERROR
        end

   | BOP binOp -> 
          let n2, n1 = pop s, pop s in
          begin 
          match n1, n2 with
          | (CST i, CST j) -> push (CST (let resu = (binOp # act (Const i) (Const j)) in
                                         begin 
                                           match resu with
                                           | Const k -> k
                                           | Bool b -> if b then 1 else 0
                                           | _ -> raise RUNTIME_ERROR
                                         end)) s ; 
                              exec s (e) c (incr_exec exec_info)
          | (REF r, CST j) -> 
                                 begin 
                                   push (CST j) s;
                                   r := j;
                                   exec s (e) c (incr_exec exec_info)
                                 end
          | _ -> raise RUNTIME_ERROR
          end

    | ACC n ->
        let o = DreamEnv.access e (n-1) in
          begin 
            push ( o) s;
            exec s e c (incr_exec exec_info)
          end

    | LET ->  
        let v = pop s in
        begin
          DreamEnv.add e v;
          exec s e c (incr_exec exec_info)
        end
  
    | ENDLET -> begin
                  DreamEnv.cut e;
                  exec s e c (incr_exec exec_info)
                end
        
    | TAILAPPLY ->
        let cst_k = pop s in
        let cls = pop s in
        begin
          match cst_k, cls with
          | CST k, CLS (c', e') -> 
              begin 
                DreamEnv.add e' (CST k);
                exec s e' c' (incr_exec exec_info)
              end
          | _ -> raise RUNTIME_ERROR
        end
    
    | EXCATCH -> 
        let cls = pop s in
        let v = pop s in
        begin
          match cls with
          | CLS (c', e') ->
              begin
                DreamEnv.add e' v;
                push (ENV e) s;
                push (CODE c) s;
                exec s e' c' (incr_exec exec_info)
              end
          | _ -> raise RUNTIME_ERROR
        end

    | APPLY ->
        let v = pop s in
        let cls = pop s in
        begin
          match cls with
          | CLS (c', e') ->
              begin
                DreamEnv.add e' v;
                push (ENV e) s;
                push (CODE c) s;
                exec s e' c' (incr_exec exec_info)
              end
          | CLSREC (c', e') ->
              let e'' = DreamEnv.copy e' in
              begin
                DreamEnv.add e' (CLSREC (c', e''));
                DreamEnv.add e' v;
                push (ENV e) s;
                push (CODE c) s;
                exec s e' c' (incr_exec exec_info)
              end
          | BUILTCLS f ->
              let _ = push (f v) s in exec s e c (incr_exec exec_info)
          | _ -> raise RUNTIME_ERROR
        end

    | RETURN ->
        let v = pop s in 
        let code_c' = pop s in 
        let env_e' = pop s 
        in 
        begin 
        match (code_c', env_e') with
        | (CODE c', ENV e') -> let _ = push v s in exec s e' c' (incr_exec exec_info)
        | _ -> raise RUNTIME_ERROR
        end
    
    | CLOSURE (c') -> let _ = push (CLS (c', DreamEnv.copy e)) s in exec s (e) c (incr_exec exec_info) 

    | CLOSUREC (c') -> let _ = push (CLSREC (c', DreamEnv.copy e)) s in exec s e c (incr_exec exec_info)

    | BUILTIN f -> let _ = push (BUILTCLS (DreamEnv.get_builtin e f)) s in exec s e c (incr_exec exec_info)

    | PROG prog_code -> 
        begin 
          push (CODE prog_code) s; 
          exec s (e) c (incr_exec exec_info) 
        end
    
    | BRANCH -> 
        let code_b = pop s
        in let code_a = pop s
        in let cst_k = pop s
        in begin
        match (cst_k, code_a, code_b) with
        | (CST k, CODE a, CODE b) -> if k = 0 then exec s (e) (b @ c) (incr_exec exec_info)
                                     else exec s (e) (a @ c) (incr_exec exec_info)
        | _ -> raise RUNTIME_ERROR
        end
  
    | TRYWITH  ->
        let code_b = pop s
        in let code_a = pop s
        in begin
        match (code_a, code_b) with
        | (CODE a, CODE b) -> begin
                              try exec s (e) (a @ c) (incr_exec exec_info)
                              with EXIT_INSTRUCTION -> exec s (e) (b @ c) (incr_exec exec_info)
                              end
        | _ -> raise RUNTIME_ERROR
        end
    
    | AMAKE ->  let v = pop s in
                begin match v with
                | CST k -> (push (ARR (Array.make k 0)) s ; exec s (e) c (incr_exec exec_info))
                | _ -> raise RUNTIME_ERROR
                end
    
    | ARRITEM -> let arr_a = pop s in
                 let cst_index = pop s in
                 begin
                 match (arr_a, cst_index) with
                 | (ARR a, CST index) ->
                        begin
                          push (CST a.(index)) s;
                          exec s (e) c (incr_exec exec_info)
                        end
                 | _ -> raise RUNTIME_ERROR
                 end

    | ARRSET -> let arr_a = pop s in
                let cst_index = pop s in
                let cst_value = pop s in               
                begin
                match (arr_a, cst_index, cst_value) with
                | (ARR a, CST index, CST value) ->
                      begin
                        a.(index) <- value;
                        exec s (e) c (incr_exec exec_info)
                      end
                | _ -> raise RUNTIME_ERROR
                end

    | PRINTIN -> 
        let v = pop s in
        begin
          match v with
          | CST k -> 
              begin
                print_endline @@ (string_of_int k);
                push (CST k) s;
                exec s e c (incr_exec exec_info)
              end
          | _ -> raise RUNTIME_ERROR
        end
                
    | EXIT -> raise EXIT_INSTRUCTION

    | PASS -> exec s e c (incr_exec exec_info)

    | _ -> failwith "not implemented in execution"

end
    
(*
let init () =
  let e = DreamEnv.init () in
  begin 
    DreamEnv.add e (CLS ([ACC 1; AMAKE; RETURN], e));
    DreamEnv.add e "prInt" (CLS ([ACC 1; PRINTIN; RETURN], e));
    e
  end
*)

let exec_wrap code exec_info = exec (Stack.create ()) (DreamEnv.init ()) code exec_info
