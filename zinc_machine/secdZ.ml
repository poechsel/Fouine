open Env
open Expr
open CompilZ
open Binop
open Stack
open DreamZ
open IsaZ
open ZincEnv

type exec_info_structure =
  {debug : bool ref;
   nb_op : int ref}

let incr_exec exec_info = 
  let _ = incr exec_info.nb_op in exec_info

let print_stack s =
    try
    let v = top s in
    "top of stack -> " ^ 
    begin
      match v with
      | CODE c -> Printf.sprintf "CODE of lines of code"
      | CLS (c, e) -> Printf.sprintf "CLOSURE of code %s " (print_code c)
      | CLSREC (c, e) -> Printf.sprintf "CLSREC of some code, some env"
      | CST k -> Printf.sprintf "CST of %s" (string_of_int k)
      | REF r -> Printf.sprintf "REF of value : %s" (string_of_int !r)
      | ARR a -> Printf.sprintf "array "
      | _ -> ""
    end
    with Stack.Empty -> Printf.sprintf "stack is empty for the moment"

exception EXIT_INSTRUCTION
exception RUNTIME_ERROR

let rec exec_zinc a s r e code exec_info =
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
                               (let v = ZincEnv.front e in 
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
        print_endline @@ Printf.sprintf "items of the env %s" (ZincEnv.print_env e);
        print_endline @@ Printf.sprintf "next instructions : %s" (print_code c);
        print_endline @@ print_stack s;
        print_endline @@ Printf.sprintf "stack size : %s" (string_of_int @@ length s);
        print_endline @@ print_instr instr 
      end;
    
    match instr with

    | C k -> let _ = push (CST k) s in exec_zinc a s r e c (incr_exec exec_info)

    | REF -> 
        let v = pop s in
        begin
          match v with
          | CST k ->
              begin
                push (REF (ref k)) s; 
                exec_zinc a s r (e) c (incr_exec exec_info)
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
              exec_zinc a s r (e) c (incr_exec exec_info)
            end
        | _ -> raise RUNTIME_ERROR
        end

   | BOP binOp -> 
          let n2, n1 = pop s, pop s in
          begin 
          match n1, n2 with
          | (CST i, CST j) -> let prim = CST (let resu = (binOp # act (Const i) (Const j)) in
                                              begin 
                                                match resu with
                                                | Const k -> k
                                                | Bool b -> if b then 1 else 0
                                                | _ -> raise RUNTIME_ERROR
                                              end) 
                              in exec_zinc prim s r (e) c (incr_exec exec_info)
          | (REF re, CST j) ->    begin 
                                   push (CST j) s;
                                   re := j;
                                   exec_zinc a s r (e) c (incr_exec exec_info)
                                 end
          | _ -> raise RUNTIME_ERROR
          end

    | ACC n ->
        let o = ZincEnv.access e (n-1) in
          begin 
            push ( o) s;
            exec_zinc a s r e c (incr_exec exec_info)
          end

    | LET -> begin
               ZincEnv.add e a;
               exec_zinc a s r e c (incr_exec exec_info)
             end
  
    | ENDLET -> begin
                  ZincEnv.cut e;
                  exec_zinc a s r e c (incr_exec exec_info)
                end

    | DUMMY -> begin
                 ZincEnv.add e DUM;
                 exec_zinc a s r e c (incr_exec exec_info)
               end

    | UPDATE -> begin
                  ZincEnv.update_last e a;
                  exec_zinc a s r e c (incr_exec exec_info)
                end

    | APPTERM -> 
        let ACCU (c1, e1) = a in
        let v = pop s in
        let _ = ZincEnv.add e1 v in exec_zinc a s r e1 c1 (incr_exec exec_info)
       (* 
    | TAILAPPLY ->
        let cst_k = pop s in
        let cls = pop s in
        begin
          match cst_k, cls with
          | CST k, CLS (c', e') -> 
              begin 
                ZincEnv.add e' (CST k);
                exec_zinc a s r e' c' (incr_exec exec_info)
              end
          | _ -> raise RUNTIME_ERROR
        end
      *)
    | EXCATCH -> 
        let cls = pop s in
        let v = pop s in
        begin
          match cls with
          | CLS (c', e') ->
              begin
                ZincEnv.add e' v;
                push (ENV e) s;
                push (CODE c) s;
                exec_zinc a s r e' c' (incr_exec exec_info)
              end
          | _ -> raise RUNTIME_ERROR
        end

    | APPLY ->
        let ACCU (c1, e1) = a and v = pop s in
        begin
          ZincEnv.add e1 v;
          push (CLS (c, e)) r;
          exec_zinc a s r e1 c1 (incr_exec exec_info)
        end

    | PUSH ->
        let _ = push a s in exec_zinc a s r e c (incr_exec exec_info)

    | PUSHMARK -> 
        let _ = push MARK s in exec_zinc a s r e c (incr_exec exec_info)

    | CUR c1 -> exec_zinc (ACCU(c1, e)) s r e c (incr_exec exec_info)

    | GRAB ->
        let v = pop s in
        begin
          match v with
          | MARK -> let ACCU (c1, e1) = pop r in
                    exec_zinc (ACCU (c, e)) s r e1 c1 (incr_exec exec_info)
          | _ -> let _ = ZincEnv.add e v in exec_zinc a s r e c (incr_exec exec_info)
        end

    | RETURN ->
        let v = pop s in
        begin
          match v with
          | MARK -> let ACCU (c1, e1) = pop r in
                    exec_zinc a s r e1 c1 (incr_exec exec_info)
          | _ -> let ACCU (c1, e1) = a in
                 let _ = ZincEnv.add e1 v in exec_zinc a s r e1 c1 (incr_exec exec_info)
        end

    | CLOSURE (c') -> let _ = push (CLS (c', ZincEnv.copy e)) s in exec_zinc a s r (e) c (incr_exec exec_info) 

    | CLOSUREC (c') -> let _ = push (CLSREC (c', ZincEnv.copy e)) s in exec_zinc a s r e c (incr_exec exec_info)

    | BUILTIN f -> let _ = push (BUILTCLS (ZincEnv.get_builtin e f)) s in exec_zinc a s r e c (incr_exec exec_info)

    | PROG prog_code -> 
        begin 
          push (CODE prog_code) s; 
          exec_zinc a s r (e) c (incr_exec exec_info) 
        end
    
    | BRANCH -> 
        let code_b = pop s
        in let code_a = pop s
        in let cst_k = pop s
        in begin
        match (cst_k, code_a, code_b) with
        | (CST k, CODE m, CODE n) -> if k = 0 then exec_zinc a s r (e) (n @ c) (incr_exec exec_info)
                                     else exec_zinc a s r (e) (m @ c) (incr_exec exec_info)
        | _ -> raise RUNTIME_ERROR
        end
  
    | TRYWITH  ->
        let code_b = pop s
        in let code_a = pop s
        in begin
        match (code_a, code_b) with
        | (CODE m, CODE n) -> begin
                              try exec_zinc a s r (e) (m @ c) (incr_exec exec_info)
                              with EXIT_INSTRUCTION -> exec_zinc a s r (e) (n @ c) (incr_exec exec_info)
                              end
        | _ -> raise RUNTIME_ERROR
        end
    
    | AMAKE ->  let v = pop s in
                begin match v with
                | CST k -> (push (ARR (Array.make k 0)) s ; exec_zinc a s r (e) c (incr_exec exec_info))
                | _ -> raise RUNTIME_ERROR
                end
    
    | ARRITEM -> let arr_a = pop s in
                 let cst_index = pop s in
                 begin
                 match (arr_a, cst_index) with
                 | (ARR m, CST index) ->
                        begin
                          push (CST m.(index)) s;
                          exec_zinc a s r (e) c (incr_exec exec_info)
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
                        exec_zinc a s r (e) c (incr_exec exec_info)
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
                exec_zinc a s r e c (incr_exec exec_info)
              end
          | _ -> raise RUNTIME_ERROR
        end
                
    | EXIT -> raise EXIT_INSTRUCTION

    | PASS -> exec_zinc a s r e c (incr_exec exec_info)

    | _ -> failwith "not implemented in execution"

end
    
let exec_wrap code exec_info = exec_zinc VOID (Stack.create ()) (Stack.create ()) (ZincEnv.init ()) code exec_info
