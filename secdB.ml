open Expr
open Shared
open Shared.Env
open CompilB
open Stack
open Dream
open DreamEnv
open Utils

(** VIRTUAL MACHINE **)

exception EXIT_INSTRUCTION
exception RUNTIME_ERROR
exception MATCH_FAILURE

(* MAIN FUNCTION *)

let rec exec s e code exec_info =
 (* try*)
  match code with 
  | [] -> print_out s e exec_info
  | instr::c ->

      let () = if !(exec_info.debug) then
        begin print_debug s e c exec_info instr;
              incr exec_info.nb_op end
      in
      match instr with
      | C k -> let _ = push (CST k) s in exec s e c exec_info 

      | B b -> let _ = push (BOOL b) s in exec s e c exec_info
          
      | REF -> 
          let v = pop s in
          let _ = push (REF (ref v)) s in exec s e c exec_info

      | BANG ->
          let r = pop_ref s in
          let _ = push !r s in exec s e c exec_info
     
     (* treats also ref values assignation *)
     | BOP binOp -> 
            let n2, n1 = pop s, pop s in
            let _ = push (process_binop binOp n1 n2) s in exec s e c exec_info

      | ACC n ->
          let o = DreamEnv.access e (n-1) in
          let _ = push o s in exec s e c exec_info 

      | LET ->  
          let v = pop s in
          let _ = DreamEnv.add e v in exec s e c exec_info
    
      | ENDLET -> 
          let _ = DreamEnv.cut e in exec s e c exec_info
      
      | TAILAPPLY ->
          let cls, v = pop s, pop s in
          begin
            match cls with
            | CLS (c', e') -> 
                let e'' = DreamEnv.copy e' in
                let _ = DreamEnv.add e' v in exec s e'' c' exec_info
            | BUILTCLS f -> let _ = push (f v) s in exec s e c exec_info
            | CLSREC (c', e') ->
                let e'' = DreamEnv.copy e' in
                let e''' = DreamEnv.copy e' in
                begin
                  DreamEnv.add e'' (CLSREC (c', e'''));
                  DreamEnv.add e'' v;
                  exec s e'' c' exec_info
                end
            | _ -> raise RUNTIME_ERROR
          end
     
      (* used for catching exceptions : for example, "with E x -> x+1" *)
      | EXCATCH -> 
          let v, (c', e') = pop s, pop_cls s in
          begin
            DreamEnv.add e' v;
            push (ENV e) s;
            push (CODE c) s;
            exec s e' c' exec_info
          end

      | APPLY ->
          let cls, v = pop s, pop s in
          begin
            match cls with
            | CLS (c', e') ->
                let e'' = DreamEnv.copy e' in
                begin
                  DreamEnv.add e'' v;
                  push (ENV e) s;
                  push (CODE c) s;
                  exec s e'' c' exec_info
                end
            | CLSREC (c', e') ->
                let e'' = DreamEnv.copy e' in
                let e''' = DreamEnv.copy e' in
                begin
                  DreamEnv.add e'' (CLSREC (c', e'''));
                  DreamEnv.add e'' v;
                  push (ENV e) s;
                  push (CODE c) s;
                  exec s e'' c' exec_info
                end
            | BUILTCLS f ->
                let _ = push (f v) s in exec s e c exec_info
            | _ -> raise RUNTIME_ERROR
          end

      | RETURN ->
          let e', c', v = pop_env s, pop_code s, pop s in 
          let _ = push v s in exec s e' c' exec_info
      
      | CLOSURE (c') -> let _ = push (CLS (c', DreamEnv.copy e)) s in exec s (e) c exec_info 

      | CLOSUREC (c') -> let _ = push (CLSREC (c', DreamEnv.copy e)) s in exec s e c exec_info

      | BUILTIN f -> let _ = push (BUILTCLS f) s in exec s e c exec_info
     
      | PROG prog_code -> let _ = push (CODE prog_code) s in exec s e c exec_info 
      
      | BRANCH -> 
          let k, a, b = pop_cst s, pop_code s, pop_code s in
          if k = 0 
            then exec s e (b @ c) exec_info
            else exec s e (a @ c) exec_info
    
      | TRYWITH  ->
          let a, b = pop_code s, pop_code s in 
          begin
            try exec s e (a @ c) exec_info
            with EXIT_INSTRUCTION -> exec s e (b @ c) exec_info
          end
      
      | AMAKE ->  
          let n = pop_cst s in
          let _ = push (ARR (Array.make n 0)) s in exec s e c exec_info
      
      | ARRITEM -> 
          let index, a = pop_cst s, pop_arr s in
          let _ = push (CST a.(index)) s in exec s e c exec_info

      | ARRSET -> 
          let value, index, a = pop_cst s, pop_cst s, pop_arr s in
          begin
            a.(index) <- value;
            push UNIT s;
            exec s e c exec_info
          end

      | PRINTIN -> 
          let r = pop_cst s in
          let _ = print_endline (string_of_int r) in
          let _ = push (CST r) s in exec s e c exec_info
                  
      | EXIT -> raise EXIT_INSTRUCTION

      | PASS -> let _ = push DUM s in exec s e c exec_info

      | UNIT -> let _ = push UNIT s in exec s e c exec_info

      | DUPL -> let _ = push (ENV (DreamEnv.copy e)) s in exec s e c exec_info

      | SWAP -> let e', v = pop_env s, pop s in
                let _ = push v s in exec s e' c exec_info

      | MATCH i -> let k = pop_cst s in
                   if k = i then exec s e c exec_info
                   else raise MATCH_FAILURE

      | PUSHMARK -> let _ = push MARK s in exec s e c exec_info

      | CONS -> let a = pop s in
                let v = pop s in
                begin
                  match v, a with
                  | MARK, TUPLE l ->
                      let _ = push (TUPLE l) s in exec s e c exec_info
                  | x, TUPLE l -> 
                      let _ = push (TUPLE (l @ [x])) s in exec s e (CONS :: c) exec_info
                  | _, x ->
                      begin
                        push v s;
                        push (TUPLE [x]) s;
                        exec s e (CONS :: c) exec_info
                        end
                end

      | UNFOLD ->
          let l = pop_tuple s in
            let rec push_list = function
            | [] -> exec s e c exec_info
            | x :: xs -> let _ = push x s in push_list xs
          in push_list l

      | _ -> failwith "not implemented in execution"

(* wrapper for easily executing code with structures initiated *)
let exec_wrap code exec_info = exec (Stack.create ()) (DreamEnv.init ()) code exec_info
