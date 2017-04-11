open Env
open Expr
open Compil
open Binop
open Stack

type env_items = EnvCST of int 
               | EnvCLOS of string*code*((env_items, type_listing) Env.t)
               | EnvUNITCLOS of code*((env_items, type_listing) Env.t)
               | EnvREF of int ref
               | EnvARR of int array 
and stack_items = CODE of code 
                | CLOS of string*code*(env_items, type_listing) Env.t 
                | UNITCLOS of code*(env_items, type_listing) Env.t
                | CST of int 
                | ENV of ((env_items, type_listing) Env.t)*string
                | SREF of int ref
                | ARR of int array
                | ID of string

(* just decided to allow env to contain CST of int as well as closures. thinks it's ok, although not sequential *)


let print_stack s =
    try
    let v = top s in
    "top of stack -> " ^ 
    begin
      match v with
      | CODE c -> Printf.sprintf "lines of code : %s" (print_code c)
      | CLOS (x, c, e) -> Printf.sprintf "CLOSURE of code %s with var %s " (print_code c) x
      | UNITCLOS (c, e) -> Printf.sprintf "UNITCLOS of code %s " (print_code c)
      | CST k -> Printf.sprintf "CST of %s" (string_of_int k)
      | ENV (e, le) -> Printf.sprintf "ENV with last element's key : %s " le       
      | SREF r -> Printf.sprintf "REF of value : %s" (string_of_int !r)
      | ARR a -> Printf.sprintf "array "
    end
    with Stack.Empty -> Printf.sprintf "stack is empty for the moment"


(* problem with env : the one of pierre uses keys, the one for secd machine sometimes looks more like a stack. so for let and endlet i don't know what to do yet *)
(* dans ma stack il y a :
*  - du code (instr list)
*  - des closures (e * code)
*  - des constantes *)
(* i'm now using dump to store old env during LET / ENDLET operations *)
(* until i implement bruijn substitution (or else), my closure have a string argument -> identifier *)

let stack_of_env o =
    match o with
    | EnvCST k -> CST k
    | EnvCLOS (x, c, e) -> CLOS (x, c, e)
    | EnvUNITCLOS (c, e) -> UNITCLOS (c, e)
    | EnvREF r -> SREF r
    | EnvARR a -> ARR a
    | _ -> failwith "cannot convert stack_item from env_item"

let env_of_stack o =
    match o with 
    | CST k -> EnvCST k
    | CLOS (x, c, e) -> EnvCLOS (x, c, e)
    | UNITCLOS (c, e) -> EnvUNITCLOS (c, e)
    | SREF r -> EnvREF r
    | ARR a -> EnvARR a
    | _ -> failwith "cannot convert env_item from stack_item"

let new_id e =
let id = ref 1 in
while (Env.mem e (string_of_int !id)) do
incr id done;
string_of_int !id

(* le is the last element add to e *)

exception EXIT_INSTRUCTION

let rec exec s (e, le) code d nbi debug =
  match code with 
  | [] -> Printf.sprintf "%s" (let v = pop s
                               in begin 
                                    match v with 
                                    | CST k -> string_of_int k
                                    | _ -> ""
                                  end)
  | instr::c ->
    begin
    if debug then begin
    print_endline @@ print_instr instr ;
    print_endline @@ print_stack s end;
    match instr with
    | C k -> (push (CST k) s ; exec s (e, le) c d (nbi + 1) debug)

    | REF k -> (push (SREF k) s; exec s (e, le) c d (nbi + 1) debug) 

    | BANG x ->
        let EnvREF k = Env.get_most_recent e x in begin push (CST !k) s; exec s (e, le) c d (nbi + 1) debug end

    | BOP binOp -> 
        let n2, n1 = pop s, pop s in
        begin 
        match n1, n2 with
        | (CST i, CST j) -> push (CST (let resu = (binOp # act (Const i) (Const j)) in
                                       begin 
                                         match resu with
                                         | Const k -> k
                                         | Bool b -> if b then 1 else 0
                                       end)) s ; 
                            exec s (e, le) c d (nbi + 1) debug
        | (SREF r, CST j) -> 
                               begin 
                                 push (CST j) s;
                                 r := j;
                                 exec s (e, le) c d (nbi + 1) debug
                               end
        end

    | ACCESS x -> 
        begin
        try 
        let o = Env.get_most_recent e x in
          begin 
              push (stack_of_env o) s ; 
              exec s (e, le) c d (nbi + 1) debug
          end
        with Not_found -> failwith ("var not in environment : " ^ (string_of_int nbi) ^ " instr executed") 
        end

    | CLOSURE (x, c') -> ( push (CLOS (x, c', e)) s ; exec s (e, le) c d (nbi + 1) debug)

    | CLOSUREC (f, x, c') -> 
        let e' = Env.add e f (EnvCLOS (x, c', e)) in 
        begin
          push (CLOS (x, c', e')) s;
          exec s (e, le) c d (nbi + 1) debug
        end

    | UNITCLOSURE (c') -> (push (UNITCLOS (c', e)) s; exec s (e, le) c d (nbi + 1) debug) 
    
    | APPLY ->
        let first_pop = pop s in 
        begin match first_pop with
        | CST v ->  let clos = pop s in 
                    begin match clos with                      
                    | CLOS (x, c', e') ->
                    begin 
                      push (ENV (e, le)) s; 
                      push (CODE c) s;
                      let e'' = Env.add e x (EnvCST v) in 
                      exec s (e'', x) c' d  (nbi + 1) debug (* c' should end by a
                      return which will resume the exec *)
                    end
                    | UNITCLOS (c', e') -> begin
                                            push (ENV (e, le)) s;
                                            push (CODE c) s;
                                            exec s (e', "") c' d (nbi + 1) debug
                                           end
                    end
        | UNITCLOS (c', e') ->
            begin
              push (ENV (e, le)) s;
              push (CODE c) s;
              exec s (e', "") c' d (nbi + 1) debug
            end
        end
      (* just put e instead of e' in the add e x, we'll see though *)

    | RETURN -> 
        let v = pop s in 
        let CODE c' = pop s in 
        let  ENV (e', le') = pop s 
        in  
          push v s; 
          exec s (e', le') c' d  (nbi + 1) debug

    | PRINTIN -> 
        let v = pop s in
        begin
          match v with
          | CST k -> begin print_int k ; print_string "\n" ; push v s ; exec s (e, le) c d  (nbi + 1) debug end
          | _ -> failwith "can't printin else than CST int"
        end

    | LET x -> 
        let v = pop s in
        begin match v with
        | _ ->
        let e' = Env.add e x (env_of_stack v) in
          push (e, le) d ; 
          exec s (e', x) c d  (nbi + 1) debug
        end
   
    | ENDLET -> let (e', le') = pop d in exec s (e', le') c d  (nbi + 1) debug

    | PROG prog_code -> begin push (CODE prog_code) s ; exec s (e, le) c d (nbi + 1) debug end

    | BRANCH -> 
        let CODE b = pop s
        in let CODE a = pop s
        in let CST k = pop s
        in if k = 0 then exec s (e, le) (b @ c) d (nbi + 1) debug
           else exec s (e, le) (a @ c) d (nbi + 1) debug
       
    | TRYWITH  ->
        let CODE b = pop s
        in let CODE a = pop s
        in begin 
        try exec s (e, le) (a @ c) d (nbi + 1) debug
        with EXIT_INSTRUCTION -> exec s (e, le) (b @ c) d (nbi + 1) debug
        end

    | ARRAY k -> (push (ARR (Array.make k 0)) s ; exec s (e, le) c d (nbi + 1) debug)
    
    | ARRITEM -> let ARR a = pop s in
                 let CST index = pop s in
                        begin
                          push (CST a.(index)) s;
                          exec s (e, le) c d (nbi + 1) debug
                        end

    | ARRSET ->
                let ARR a = pop s in
                let CST index = pop s in
                let CST value = pop s in                
                begin
                  a.(index) <- value;
                  exec s (e, le) c d (nbi + 1) debug
                end

    | EXIT -> raise EXIT_INSTRUCTION 

    | _ -> failwith "not implemented "
end


let exec_wrap code debug = exec (Stack.create ()) (Env.create, "") code (Stack.create ()) 0 debug

