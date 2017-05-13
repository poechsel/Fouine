open Expr
open Shared
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
          let v = pop s in
          let _ = push !(get_ref v) s in exec s e c exec_info
     
     (* treats all binary operations even switching ref values *)
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
          let v = pop s in
          let cls = pop s in
          begin
            match cls with
            | CLS (c', e') -> let _ = DreamEnv.add e' v in exec s e' c' exec_info
            | BUILTCLS f ->
                let _ = push (f v) s in exec s e c exec_info
            | _ -> raise RUNTIME_ERROR
          end
     
      (* used for catching exceptions : for example, "with E x -> x+1" *)
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
                  exec s e' c' exec_info
                end
            | _ -> raise RUNTIME_ERROR
          end

      | APPLY ->
          let v = pop s in
          let cls = pop s in
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
          let v = pop s in 
          let c' = pop s in 
          let e' = pop s in
          let _ = push v s in exec s (get_env e') (get_code c') exec_info
      
      | CLOSURE (c') -> let _ = push (CLS (c', DreamEnv.copy e)) s in exec s (e) c exec_info 

      | CLOSUREC (c') -> let _ = push (CLSREC (c', DreamEnv.copy e)) s in exec s e c exec_info


      | BUILTIN f -> let _ = push (BUILTCLS f) s in exec s e c exec_info
     
      | PROG prog_code -> let _ = push (CODE prog_code) s in exec s e c exec_info 
      
      | BRANCH -> 
          let code_b = pop s
          in let code_a = pop s
          in let cst_k = pop s
          in begin
          match (cst_k, code_a, code_b) with
          | (CST k, CODE a, CODE b) -> if k = 0 then exec s (e) (b @ c) exec_info
                                       else exec s (e) (a @ c) exec_info
          | _ -> raise RUNTIME_ERROR
          end
    
      | TRYWITH  ->
          let b = pop s in 
          let a = pop s in 
          begin
            try exec s e ((get_code a) @ c) exec_info
            with EXIT_INSTRUCTION -> exec s e ((get_code b) @ c) exec_info
          end
      
      | AMAKE ->  
          let v = pop s in
          let _ = push (ARR (Array.make (get_cst v) 0)) s in exec s e c exec_info
      
      | ARRITEM -> 
          let a = pop s in
          let i = pop s in
          let _ = push (CST (get_arr a).(get_cst i)) s in exec s e c exec_info

      | ARRSET -> let arr_a = pop s in
                  let cst_index = pop s in
                  let cst_value = pop s in               
                  begin
                  match (arr_a, cst_index, cst_value) with
                  | (ARR a, CST index, CST value) ->
                        begin
                          a.(index) <- value;
                          exec s (e) c exec_info
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
                  exec s e c exec_info
                end
            | _ -> raise RUNTIME_ERROR
          end
                  
      | EXIT -> raise EXIT_INSTRUCTION

      | PASS -> exec s e c exec_info

      | UNIT -> let _ = push UNIT s in exec s e c exec_info

      | DUPL -> let _ = push (ENV (DreamEnv.copy e)) s in exec s e c exec_info

      | SWAP -> let v1 = pop s in
                let env = pop s in
                begin
                  match env with
                  | ENV e' -> let _ = push v1 s in exec s e' c exec_info
                  | _ -> raise RUNTIME_ERROR
                end

   (*   | CONS -> let v2 = pop s in
                let v1 = pop s in
                let _ = push (CONS (v1, v2)) s in exec s e c exec_info *)

      | MATCH i -> let v = pop s in
                 begin
                   match v with 
                   | CST k when k = i -> exec s e c exec_info
                   | _ -> raise MATCH_FAILURE
                 end

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
          let v = pop s in
          begin
            match v with
            | TUPLE l -> 
                let rec push_list = function
                  | [] -> exec s e c exec_info
                  | x :: xs -> let _ = push x s in push_list xs
                in push_list l
            | _ -> raise RUNTIME_ERROR
          end

      | _ -> failwith "not implemented in execution"

  (*with EXIT_INSTRUCTION -> "Program ended itself."*)

(* wrapper for easily executing code with structures initiated *)
let exec_wrap code exec_info = exec (Stack.create ()) (DreamEnv.init ()) code exec_info
