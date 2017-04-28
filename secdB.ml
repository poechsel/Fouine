open Env
open Expr
open CompilB
open Binop
open Stack
open Dream
open Isa

(*
type env_items = EnvCST of int 
               | EnvCLOS of string*code*((env_items, type_listing) Env.t)
               | EnvUNITCLOS of code*((env_items, type_listing) Env.t)
               | EnvREF of int ref
               | EnvARR of int array 
               | EnvCODE of code
*)
type stack_items = CODE of code 
                | CLOS of code * DreamEnv.dream
                | CLOSREC of code * DreamEnv.dream
               (* | UNITCLOS of code*(env_items, type_listing) Env.t *)
                | CST of int 
                | SREF of int ref
                | ARR of int array
                | ID of string
                | ENV of DreamEnv.dream

let print_stack s =
    try
    let v = top s in
    "top of stack -> " ^ 
    begin
      match v with
      | CODE c -> Printf.sprintf "lines of code : %s" (print_code c)
      | CLOS (c, e) -> Printf.sprintf "CLOSURE of code %s " (print_code c)
      | CLOSREC (c, e) -> Printf.sprintf "CLOSREC of some code, some env"
      | CST k -> Printf.sprintf "CST of %s" (string_of_int k)
      | SREF r -> Printf.sprintf "REF of value : %s" (string_of_int !r)
      | ARR a -> Printf.sprintf "array "
      | _ -> ""
    end
    with Stack.Empty -> Printf.sprintf "stack is empty for the moment"


(* dans ma stack il y a :
*  - du code (instr list)
*  - des closures (e * code)
*  - des constantes *)
(* i'm now using dump to store old env during LET / ENDLET operations *)

let stack_of_env o =
    match o with
    | DreamEnv.EnvCST k -> CST k
    | DreamEnv.EnvCLS (c, e) -> CLOS (c, e)
    | DreamEnv.EnvCLSREC (c, e) -> CLOSREC (c, e)
    | DreamEnv.EnvREF r -> SREF r
(*    | EnvCLOS (x, c, e) -> CLOS (x, c, e) *)
(*    | EnvARR a -> ARR a
    | EnvCODE c -> CODE c
*)
let env_of_stack o =
    match o with 
    | CST k -> DreamEnv.EnvCST k
    | SREF r -> DreamEnv.EnvREF r
    | CLOS (c, e) -> DreamEnv.EnvCLS (c, e)
    | CLOSREC (c, e) -> DreamEnv.EnvCLSREC (c, e)
    (* |UNITCLOS (c, e) -> EnvUNITCLOS (c, e)
    | SREF r -> EnvREF r
    | ARR a -> EnvARR a
    | CODE c -> EnvCODE c
    | _ -> failwith "WRONG_CONVERSION_ENV_FROM_STACK"
*)

exception EXIT_INSTRUCTION
exception RUNTIME_ERROR

let rec exec s e code d nbi debug =
  match code with 
  | [] -> Printf.sprintf "- : %s" 
                              begin
                              try
                              (let v = pop s
                               in begin 
                                    match v with 
                                    | CST k -> string_of_int k
                                    | (CLOS (c, e) | CLOSREC (c, e)) -> print_code c
                                    | _ -> "not found"
                                  end)
                              with _ -> 
                               (let v = DreamEnv.front e in 
                                begin 
                                  match v with 
                                    | EnvCST k -> string_of_int k
                                    | (EnvCLS (c, _) | EnvCLSREC (c, _)) -> print_code c
                                    | _ -> "result not printable"
                                end)
                              end
  | instr::c ->
    begin
    if debug then begin
      print_endline @@ Printf.sprintf "\n%s-th instruction" (string_of_int nbi);
      print_endline @@ Printf.sprintf "items of the env %s" (DreamEnv.print_env e);
      print_endline @@ Printf.sprintf "next instructions : %s" (print_code c);
      print_endline @@ print_stack s;
      print_endline @@ print_instr instr 
    end;
    match instr with

    | C k -> 
        begin
          push (CST k) s; 
          exec s e c d (nbi + 1) debug
        end
        
    | REF -> 
        let v = pop s in
        begin
          match v with
          | CST k ->
              begin
                push (SREF (ref k)) s; 
                exec s (e) c d (nbi + 1) debug
              end
          | (CLOS _ | CLOSREC _) -> failwith "ref fun not implemented"
        end

    | BANG ->
        let v = pop s in
        begin 
        match v with
        | SREF k -> 
            begin 
              push (CST !k) s; 
              exec s (e) c d (nbi + 1) debug
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
                              exec s (e) c d (nbi + 1) debug
          | (SREF r, CST j) -> 
                                 begin 
                                   push (CST j) s;
                                   r := j;
                                   exec s (e) c d (nbi + 1) debug
                                 end
          | _ -> raise RUNTIME_ERROR
          end

    | ACC n ->
        let o = DreamEnv.access e (n-1) in
          begin 
            push (stack_of_env o) s;
            exec s e c d (nbi + 1) debug
          end

    | LET ->  
        let v = pop s in
        begin
          DreamEnv.add e (env_of_stack v);
          exec s e c d (nbi + 1) debug
        end
   
    | ENDLET -> begin
                  DreamEnv.pop e;
                  exec s e c d (nbi + 1) debug
                end
        
    | TAILAPPLY ->
        let CST k = pop s in
        let CLOS (c', e') = pop s in
        begin 
          DreamEnv.add e' (EnvCST k);
          exec s e' c' d (nbi + 1) debug
        end

    | APPLY ->
        let CST k = pop s in
        let cls = pop s in
        begin
          match cls with
          | CLOS (c', e') ->
              begin
                DreamEnv.add e' (EnvCST k);
                push (ENV e) s;
                push (CODE c) s;
                exec s e' c' d (nbi + 1) debug
              end
          | CLOSREC (c', e') ->
              let e'' = DreamEnv.copy e' in
              begin
                DreamEnv.add e' (EnvCLSREC (c', e''));
                DreamEnv.add e' (EnvCST k);
                push (ENV e) s;
                push (CODE c) s;
                exec s e' c' d (nbi + 1) debug
              end
        end
	
    | RETURN ->
        let v = pop s in 
        let code_c' = pop s in 
        let env_e' = pop s 
        in 
        begin 
        match (code_c', env_e') with
        | (CODE c', ENV e') -> begin
                               push v s;
                               exec s e' c' d (nbi + 1) debug
                               end
        | _ -> raise RUNTIME_ERROR
        end
    
    | CLOSURE (c') ->
        begin
          push (CLOS (c', DreamEnv.copy e)) s;
          exec s (e) c d (nbi + 1) debug 
        end

    | CLOSUREC (c') -> 
        begin
          push (CLOSREC (c', DreamEnv.copy e)) s;
          exec s e c d (nbi + 1) debug
        end

    | PROG prog_code -> 
        begin 
          push (CODE prog_code) s; 
          exec s (e) c d (nbi + 1) debug 
        end
    
    | BRANCH -> 
        let code_b = pop s
        in let code_a = pop s
        in let cst_k = pop s
        in begin
        match (cst_k, code_a, code_b) with
        | (CST k, CODE a, CODE b) -> if k = 0 then exec s (e) (b @ c) d (nbi + 1) debug
                                     else exec s (e) (a @ c) d (nbi + 1) debug
        | _ -> raise RUNTIME_ERROR
        end
    
    | TRYWITH  ->
        let code_b = pop s
        in let code_a = pop s
        in begin
        match (code_a, code_b) with
        | (CODE a, CODE b) -> begin
                              try exec s (e) (a @ c) d (nbi + 1) debug
                              with EXIT_INSTRUCTION -> exec s (e) (b @ c) d (nbi + 1) debug
                              end
        | _ -> raise RUNTIME_ERROR
        end
    
    (*
    | AMAKE ->  let v = pop s in
                begin match v with
                | CST k -> (push (ARR (Array.make k 0)) s ; exec s (e) c d (nbi + 1) debug)
                | _ -> raise RUNTIME_ERROR
                end
    
    | ARRITEM -> let arr_a = pop s in
                 let cst_index = pop s in
                 begin
                 match (arr_a, cst_index) with
                 | (ARR a, CST index) ->
                        begin
                          push (CST a.(index)) s;
                          exec s (e) c d (nbi + 1) debug
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
                        exec s (e) c d (nbi + 1) debug
                      end
                | _ -> raise RUNTIME_ERROR
                end
    *)

    | PRINTIN -> 
        let v = pop s in
        begin
          match v with
          | CST k -> 
              begin
                print_endline @@ (string_of_int k);
                push (CST k) s;
                exec s e c d (nbi + 1) debug
              end
          | _ -> raise RUNTIME_ERROR
        end
                
    | EXIT -> raise EXIT_INSTRUCTION

end
    
(*
let init () =
  let e = DreamEnv.init () in
  begin 
    DreamEnv.add e (EnvCLS ([ACC 1; AMAKE; RETURN], e));
    DreamEnv.add e "prInt" (EnvCLS ([ACC 1; PRINTIN; RETURN], e));
    e
  end
*)

let exec_wrap code debug = exec (Stack.create ()) (DreamEnv.init ()) code (Stack.create ()) 1 debug
