open Env
open Expr
open CompilB
open Binop
open Stack
open Dream
open Isa
open DreamEnv

(** DEBUGGING ELEMENTS **)

type exec_info_structure =
  {debug : bool ref;
   nb_op : int ref}

(* shortcuts for improving readbility of the code *)
let pe = print_endline and pf = Printf.sprintf

let incr_exec exec_info = 
  let _ = incr exec_info.nb_op in exec_info

(* prints the element on top of the stack *)
let print_stack s =
    try
    let v = top s in
    "top of stack -> " ^ 
    begin
      match v with
      | CODE c -> pf "lines of code : %s" (print_code c)
      | CLS (c, e) -> pf "CLOSURE of code %s " (print_code c)
      | CLSREC (c, e) -> pf "CLSREC of some code, some env"
      | CST k -> pf "CST of %s" (string_of_int k)
      | REF r -> pf "REF value" 
      | ARR a -> pf "array "
      | _ -> ""
    end
    with Stack.Empty -> pf "stack is empty for the moment"

(* function printing debug informations *)
let print_debug s e c exec_info instr =
  begin
    pe @@ pf "\n%s-th instruction" (string_of_int !(exec_info.nb_op));
    pe @@ pf "env size : %s" (string_of_int @@ size e);
    pe @@ pf "items of the env %s" (DreamEnv.print_env e);
    pe @@ pf "next instructions : %s" (print_code c);
    pe @@ print_stack s;
    pe @@ pf "stack size : %s" (string_of_int @@ length s);
    pe @@ print_instr instr 
  end

(** END debugging **)



(* printing functions, called when computation is over *)

let print_item i =
  match i with 
  | CST k -> string_of_int k
  | (CLS (c, e) | CLSREC (c, e)) -> print_code c
  | _ -> ""

let print_out s e =
  "- : " ^ 
  begin 
    try print_item (pop s)
    with _ ->
      try print_item (DreamEnv.front e)
      with _ -> "()"
  end


(** VIRTUAL MACHINE **)

exception EXIT_INSTRUCTION
exception RUNTIME_ERROR


(* MAIN FUNCTION *)

let rec exec s e code exec_info =
  match code with 
  | [] -> print_out s e 
  | instr::c ->

      let _ =  if !(exec_info.debug) then print_debug s e c exec_info instr
      in
      match instr with

      | C k -> let _ = push (CST k) s in exec s e c (incr_exec exec_info) 
          
      | REF -> 
          let v = pop s in
          let _ = push (REF (ref v)) s in exec s e c (incr_exec exec_info)

      | BANG ->
          let v = pop s in
          begin 
          match v with
          | REF k -> let _ = push !k s in exec s e c (incr_exec exec_info) 
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
            | (REF r, CST j) ->   begin 
                                     push (CST j) s;
                                     r := (CST j);
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

      
let exec_wrap code exec_info = exec (Stack.create ()) (DreamEnv.init ()) code exec_info
