open Expr
open CompilZ
open Stack
open Dream
open DreamEnv
open Utils


exception EXIT_INSTRUCTION
exception RUNTIME_ERROR

let rec exec_zinc a s r e code exec_info =
  match code with 
  | [] -> "- : " ^ print_item a 
  | instr::c ->

    begin
    let () = if !(exec_info.debug) then
             begin print_debug s e c exec_info instr;
                   print_endline ("== " ^ "Accumulator : " ^ (print_env_item a));
                   print_endline "\n";
                   incr exec_info.nb_op end
    in 
    match instr with

    | C k -> exec_zinc (CST k) s r e c exec_info

    | REF -> 
        let v = pop s in
        let _ = push (REF (ref v)) s in exec_zinc a s r e c exec_info

    | BANG ->
        let v = pop s in
        begin 
        match v with
        | REF k -> 
            begin 
              push !k s; 
              exec_zinc a s r (e) c exec_info
            end
        | _ -> raise RUNTIME_ERROR
        end
    
    | BOP binOp ->
             let n2, n1 = pop s, pop s in
             let prim = process_binop binOp n1 n2 in exec_zinc prim s r e c exec_info
 
    | ACC n ->
        let o = DreamEnv.access e (n-1) in
          begin 
            exec_zinc o s r e c exec_info
          end

    | LET -> begin
               DreamEnv.add e a;
               exec_zinc a s r e c exec_info
             end
  
    | ENDLET -> begin
                  DreamEnv.cut e;
                  exec_zinc a s r e c exec_info
                end

    | DUMMY -> begin
                 DreamEnv.add e ZDUM;
                 exec_zinc a s r e c exec_info
               end
(*  todo
    | UPDATE -> begin
                  DreamEnv.update_last e a;
                  exec_zinc a s r e c exec_info
                end
*)
    | APPTERM -> 
        let (c1, e1) = get_cls a in
        let v = pop s in
        let _ = DreamEnv.add e1 v in exec_zinc a s r e1 c1 exec_info
    
    | EXCATCH -> 
        let (c', e') = pop_cls s in (* on extrait les éléments de la closure *)
        let v = pop s in
        begin
          DreamEnv.add e' v;
          push (ENV e) s;
          push (CODE c) s;
          exec_zinc a s r e' c' exec_info
        end

    | APPLY ->
        let v = pop s in
        begin
          match a with
          | CLS (c1, e1) ->
              begin
                let e1' = DreamEnv.copy e1 in
                DreamEnv.add e1' v;
                push (CLS (c, e)) r;
                exec_zinc a s r e1' c1 exec_info
              end
          | CLSREC (c1, e1) -> 
                let e1' = DreamEnv.copy e1 in
                let e1'' = DreamEnv.copy e1 in
                begin
                  DreamEnv.add e1' (CLSREC (c1, e1''));
                  DreamEnv.add e1' v;
                  push (CLSREC (c1, DreamEnv.copy e1)) r;
                  exec_zinc a s r e1' c1 exec_info
                end
          | BUILTCLS f ->
              let _ = push (f v) s in
              let _ = push (BUILTCLS f) r in exec_zinc a s r e c exec_info
          | _-> raise RUNTIME_ERROR
        end


    | PUSH ->
        let _ = push a s in exec_zinc a s r e c exec_info

    | PUSHMARK -> 
        let _ = push ZMARK s in exec_zinc a s r e c exec_info

    | CUR c1 -> exec_zinc (CLS(c1, DreamEnv.copy e)) s r e c exec_info

    | GRAB ->
        let v = pop s in
        begin
          match v with
          | ZMARK -> begin
                    let cls = pop r in 
                      match cls with
                      | CLS (c1, e1) ->
                          exec_zinc (CLS (c, e)) s r e1 c1 exec_info
                      | CLSREC (c1, e1) -> 
                          exec_zinc (CLSREC (c, e)) s r e1 c1 exec_info
                      | BUILTCLS f ->
                          exec_zinc (BUILTCLS f) s r e c exec_info
                      | _-> raise RUNTIME_ERROR
                    end
          | _ -> let _ = DreamEnv.add e v in exec_zinc a s r e c exec_info
        end

    | RETURN ->
        let v = pop s in
        begin
          match v with
          | ZMARK -> let (c1, e1) = pop_cls r in 
                    exec_zinc a s r e1 c1 exec_info
          | _ -> let (c1, e1) = get_cls a in
                 let e1' = DreamEnv.copy e1 in
                 let _ = DreamEnv.add e1' v in exec_zinc a s r e1' c1 exec_info
        end

    | CLOSURE (c') -> exec_zinc (CLS (c', DreamEnv.copy e)) s r (e) c exec_info 

    | CLOSUREC (c') -> exec_zinc (CLSREC (c', DreamEnv.copy e)) s r e c exec_info

    | BUILTIN f -> exec_zinc (BUILTCLS f) s r e c exec_info

    | PROG prog_code -> 
        begin 
          push (CODE prog_code) s; 
          exec_zinc a s r (e) c exec_info 
        end
    
    | BRANCH -> 
        let code_b = pop s
        in let code_a = pop s
        in let cst_k = pop s
        in begin
        match (cst_k, code_a, code_b) with
        | (CST k, CODE m, CODE n) -> if k = 0 then exec_zinc a s r (e) (n @ c) exec_info
                                     else exec_zinc a s r (e) (m @ c) exec_info
        | _ -> raise RUNTIME_ERROR
        end
  
    | TRYWITH  ->
        let code_b = pop s
        in let code_a = pop s
        in begin
        match (code_a, code_b) with
        | (CODE m, CODE n) -> begin
                              try exec_zinc a s r (e) (m @ c) exec_info
                              with EXIT_INSTRUCTION -> exec_zinc a s r (e) (n @ c) exec_info
                              end
        | _ -> raise RUNTIME_ERROR
        end
    
    | AMAKE ->  let v = pop s in
                begin match v with
                | CST k -> (push (ARR (Array.make k 0)) s ; exec_zinc a s r (e) c exec_info)
                | _ -> raise RUNTIME_ERROR
                end
    
    | ARRITEM -> let arr_a = pop s in
                 let cst_index = pop s in
                 begin
                 match (arr_a, cst_index) with
                 | (ARR m, CST index) ->
                        begin
                          push (CST m.(index)) s;
                          exec_zinc a s r (e) c exec_info
                        end
                 | _ -> raise RUNTIME_ERROR
                 end

    | ARRSET -> let arr_a = pop s in
                let cst_index = pop s in
                let cst_value = pop s in               
                begin
                match (arr_a, cst_index, cst_value) with
                | (ARR m, CST index, CST value) ->
                      begin
                        m.(index) <- value;
                        exec_zinc a s r (e) c exec_info
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
                exec_zinc a s r e c exec_info
              end
          | _ -> raise RUNTIME_ERROR
        end
                
    | EXIT -> raise EXIT_INSTRUCTION

    | PASS -> exec_zinc a s r e c exec_info

    | _ -> failwith "not implemented in execution"

end
    
let exec_wrap_Z code exec_info = exec_zinc VOID (Stack.create ()) (Stack.create ()) (DreamEnv.init ()) code exec_info
