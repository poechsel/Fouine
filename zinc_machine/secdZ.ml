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
   nb_op : int ref;
  t : float}

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

let pe = print_endline and pf = Printf.sprintf

(* function printing debug informations *)
let print_debug a s e c exec_info instr =
  begin
    pe @@ pf "\n%s-th instruction" (string_of_int !(exec_info.nb_op));
    pe @@ pf "env size : %s" (string_of_int @@ size e);
    pe @@ pf "items of the env %s" (ZincEnv.print_env e);
    pe @@ pf "next instructions : %s" (print_code c);
    pe @@ print_stack s;
    pe @@ pf "stack size : %s" (string_of_int @@ length s);
    pe @@ pf "the accumulator : %s" (print_item a);
    pe @@ print_instr instr
  end

exception EXIT_INSTRUCTION
exception RUNTIME_ERROR

let is_cls = function
  | (CLS _ | CLSREC _) -> true
  | _ -> false

let extr_cls = function
  | CLS (c1, e1) -> (c1, e1)
  | CLSREC (c1, e1) -> (c1, e1)
  | _ -> raise RUNTIME_ERROR

let print_item i =
  match i with
  | CST k -> string_of_int k
  | (CLS (c, e) | CLSREC (c, e)) -> print_code c
  | _ -> ""

let rec exec_zinc a s r e code exec_info =
  match code with 
  | [] -> "- : " ^ print_item a 
  | instr::c ->

    begin
      
      if !(exec_info.debug) then print_debug a s e c exec_info instr ;
    
    match instr with

    | C k -> exec_zinc (CST k) s r e c (incr_exec exec_info)

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
          begin
          match a, (pop s) with
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
            exec_zinc o s r e c (incr_exec exec_info)
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
        let (c1, e1) = extr_cls a in
        let v = pop s in
        let _ = ZincEnv.add e1 v in exec_zinc a s r e1 c1 (incr_exec exec_info)
    
    | EXCATCH -> 
        let (c', e') = extr_cls (pop s) in (* on extrait les éléments de la closure *)
        let v = pop s in
        begin
          ZincEnv.add e' v;
          push (ENV e) s;
          push (CODE c) s;
          exec_zinc a s r e' c' (incr_exec exec_info)
        end

    | APPLY ->
        let v = pop s in
        begin
          match a with
          | CLS (c1, e1) ->
              begin
                let e1' = ZincEnv.copy e1 in
                ZincEnv.add e1' v;
                push (CLS (c, e)) r;
                exec_zinc a s r e1' c1 (incr_exec exec_info)
              end
          | CLSREC (c1, e1) -> 
                let e1' = ZincEnv.copy e1 in
                let e1'' = ZincEnv.copy e1 in
                begin
                  ZincEnv.add e1' (CLSREC (c1, e1''));
                  ZincEnv.add e1' v;
                  push (CLSREC (c1, ZincEnv.copy e1)) r;
                  exec_zinc a s r e1' c1 (incr_exec exec_info)
                end
          | _-> raise RUNTIME_ERROR
        end


    | PUSH ->
        let _ = push a s in exec_zinc a s r e c (incr_exec exec_info)

    | PUSHMARK -> 
        let _ = push MARK s in exec_zinc a s r e c (incr_exec exec_info)

    | CUR c1 -> exec_zinc (CLS(c1, ZincEnv.copy e)) s r e c (incr_exec exec_info)

    | GRAB ->
        let v = pop s in
        begin
          match v with
          | MARK -> begin
                    let cls = pop r in 
                      match cls with
                      | CLS (c1, e1) ->
                          exec_zinc (CLS (c, e)) s r e1 c1 (incr_exec exec_info)
                      | CLSREC (c1, e1) -> 
                          exec_zinc (CLSREC (c, e)) s r e1 c1 (incr_exec exec_info)
                      | _-> raise RUNTIME_ERROR
                    end
          | _ -> let _ = ZincEnv.add e v in exec_zinc a s r e c (incr_exec exec_info)
        end

    | RETURN ->
        let v = pop s in
        begin
          match v with
          | MARK -> let (c1, e1) = extr_cls ( pop r ) in 
                    exec_zinc a s r e1 c1 (incr_exec exec_info)
          | _ -> let (c1, e1) = extr_cls a in
                 let e1' = ZincEnv.copy e1 in
                 let _ = ZincEnv.add e1' v in exec_zinc a s r e1' c1 (incr_exec exec_info)
        end

    | CLOSURE (c') -> exec_zinc (CLS (c', ZincEnv.copy e)) s r (e) c (incr_exec exec_info) 

    | CLOSUREC (c') -> exec_zinc (CLSREC (c', ZincEnv.copy e)) s r e c (incr_exec exec_info)

    | BUILTIN f -> exec_zinc (BUILTCLS (ZincEnv.get_builtin e f)) s r e c (incr_exec exec_info)

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
