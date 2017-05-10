open Expr
open Shared
open CompilB
open Stack
open Dream
open DreamEnv

(** DEBUGGING ELEMENTS **)

type exec_info_structure =
  {debug : bool ref;
   nb_op : int ref; 
   t : float}

(* shortcuts for improving readability of the printing functions *)
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
      | CODE c -> pf "lines of code : %s" (print_code c false)
      | CLS (c, e) -> pf "CLOSURE of code %s " (print_code c false)
      | CLSREC (c, e) -> pf "CLSREC of some code, some env"
      | CST k -> pf "CST of %s" (string_of_int k)
      | REF r -> pf "REF value" 
      | ARR a -> pf "array "
      | TUPLE l -> pf "tuple of length %s" (string_of_int (List.length l))
      | _ -> ""
    end
    with Stack.Empty -> pf "stack is empty for the moment"

(* function printing debug informations *)
let print_debug s e c exec_info instr =
  begin
    pe @@ pf "\n%s-th instruction" (string_of_int !(exec_info.nb_op));
    pe @@ pf "env size: %s" (string_of_int @@ size e);
    pe @@ pf "items of the env %s" (DreamEnv.print_env e);
    pe @@ pf "next instructions:%s" (print_code c false);
    pe @@ print_stack s;
    pe @@ pf "stack size: %s" (string_of_int @@ length s);
    pe @@ print_instr instr 
  end

(** END debugging **)


(* printing functions, called when computation is over *)

let print_item i =
  match i with 
  | CST k -> string_of_int k
  | (CLS (c, e) | CLSREC (c, e)) -> print_code c false
  | _ -> ""

(* prints the result of computation as well as the running time of the program
 * if the option is enabled *)
let print_out s e exec_info =
  let _ = if !(exec_info.debug) then print_endline @@ "\nRunning time : " ^ (string_of_float (Unix.gettimeofday () -. exec_info.t)) else () 
  in
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
exception MATCH_FAILURE (* future tuple implementation *)

(* MAIN FUNCTION *)

let rec exec s e code exec_info =
 (* try*)
  match code with 
  | [] -> print_out s e exec_info
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
     
     (* treats all binary operations - even switching ref values *)
     | BOP binOp -> 
            let n2, n1 = pop s, pop s in
            begin 
            match n1, n2 with
            | (CST i, CST j) -> push (CST (let resu = (binOp # act (FInt i) (FInt j)) in
                                           begin 
                                             match resu with
                                             | FInt k -> k
                                             | FBool b -> if b then 1 else 0
                                             | _ -> raise RUNTIME_ERROR
                                           end)) s ; 
                                exec s (e) c (incr_exec exec_info)
            | (REF r, _) ->   begin 
                                     push n2 s;
                                     r := n2;
                                     exec s (e) c (incr_exec exec_info)
                                   end
            | _ -> raise RUNTIME_ERROR
            end

      | ACC n ->
          let o = DreamEnv.access e (n-1) in
          let _ = push o s in exec s e c (incr_exec exec_info) 

      | LET ->  
          let v = pop s in
          let _ = DreamEnv.add e v in exec s e c (incr_exec exec_info)
    
      | ENDLET -> 
          let _ = DreamEnv.cut e in exec s e c (incr_exec exec_info)
      
      | TAILAPPLY ->
          let v = pop s in
          let cls = pop s in
          begin
            match cls with
            | CLS (c', e') -> let _ = DreamEnv.add e' v in exec s e' c' (incr_exec exec_info)
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
                let e'' = DreamEnv.copy e' in
                begin
                  DreamEnv.add e'' v;
                  push (ENV e) s;
                  push (CODE c) s;
                  exec s e'' c' (incr_exec exec_info)
                end
            | CLSREC (c', e') ->
                let e'' = DreamEnv.copy e' in
                let e''' = DreamEnv.copy e' in
                begin
                  DreamEnv.add e'' (CLSREC (c', e'''));
                  DreamEnv.add e'' v;
                  push (ENV e) s;
                  push (CODE c) s;
                  exec s e'' c' (incr_exec exec_info)
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
      
      | CLOSURE (c')   -> let _ = push (CLS (c', DreamEnv.copy e)) s in exec s (e) c (incr_exec exec_info) 

      | CLOSUREC (c')  -> let _ = push (CLSREC (c', DreamEnv.copy e)) s in exec s e c (incr_exec exec_info)


      | BUILTIN f      -> let _ = push (BUILTCLS f) s in exec s e c (incr_exec exec_info)
     
      | PROG prog_code -> let _ = push (CODE prog_code) s in exec s e c (incr_exec exec_info) 
      
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
          let code_b = pop s in 
          let code_a = pop s in 
          begin
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
                           let _ = push (CST a.(index)) s in exec s e c (incr_exec exec_info)
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

      | UNIT -> let _ = push UNIT s in exec s e c (incr_exec exec_info)

      | DUPL -> let _ = push (ENV (DreamEnv.copy e)) s in exec s e c (incr_exec exec_info)

      | SWAP -> let v1 = pop s in
                let env = pop s in
                begin
                  match env with
                  | ENV e' -> let _ = push v1 s in exec s e' c (incr_exec exec_info)
                  | _ -> raise RUNTIME_ERROR
                end

   (*   | CONS -> let v2 = pop s in
                let v1 = pop s in
                let _ = push (CONS (v1, v2)) s in exec s e c (incr_exec exec_info) *)

      | MATCH i -> let v = pop s in
                 begin
                   match v with 
                   | CST k when k = i -> exec s e c (incr_exec exec_info)
                   | _ -> raise MATCH_FAILURE
                 end

      | PUSHMARK -> let _ = push MARK s in exec s e c (incr_exec exec_info)

      | CONS -> let a = pop s in
                  let v = pop s in
                  begin
                    match v, a with
                    | MARK, TUPLE l ->
                        let _ = push (TUPLE l) s in exec s e c (incr_exec exec_info)
                    | x, TUPLE l -> 
                        let _ = push (TUPLE (l @ [x])) s in exec s e (CONS :: c) (incr_exec exec_info)
                    | _, x ->
                        begin
                          push v s;
                          push (TUPLE [x]) s;
                          exec s e (CONS :: c) (incr_exec exec_info)
                        end
                  end

      | UNFOLD ->
          let v = pop s in
          begin
            match v with
            | TUPLE l -> 
                let rec push_list = function
                  | [] -> exec s e c (incr_exec exec_info)
                  | x :: xs -> let _ = push x s in push_list xs
                in push_list l
            | _ -> raise RUNTIME_ERROR
          end

      | _ -> failwith "not implemented in execution"

  (*with EXIT_INSTRUCTION -> "Program ended itself."*)

(* wrapper for easily executing code with structures initiated *)
let exec_wrap code exec_info = exec (Stack.create ()) (DreamEnv.init ()) code exec_info
