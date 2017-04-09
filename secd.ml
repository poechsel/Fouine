open Env
open Expr
open Compil
open Binop
open Stack

type env_items = EnvCST of int 
               | EnvCLOS of string*code*((env_items, type_listing) Env.t)
               | EnvREF of int ref
and stack_items = CODE of code 
                | CLOS of string*code*(env_items, type_listing) Env.t 
                | CST of int 
                | ENV of ((env_items, type_listing) Env.t)*string
                | SREF of int ref

(* just decided to allow env to contain CST of int as well as closures. thinks it's ok, although not sequential *)


let print_stack s =
    try
    let v = top s in
    begin
      match v with
      | CODE c -> Printf.sprintf "lines of code : %s" (print_code c)
      | CLOS (x, c, e) -> Printf.sprintf "CLOSURE of code %s with var %s " (print_code c) x
      | CST k -> Printf.sprintf "CST of %s" (string_of_int k)
      | ENV (e, le) -> Printf.sprintf "ENV with last element's key : %s " le       
      | SREF r -> Printf.sprintf "REF of value : %s" (string_of_int !r)
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
    | EnvREF r -> SREF r
    | _ -> failwith "cannot convert stack_item from env_item"

let env_of_stack o =
    match o with 
    | CST k -> EnvCST k
    | CLOS (x, c, e) -> EnvCLOS (x, c, e)
    | SREF r -> EnvREF r
    | _ -> failwith "cannot convert env_item from stack_item"

let new_id e =
let id = ref 1 in
while (Env.mem e (string_of_int !id)) do
incr id done;
string_of_int !id

(* le is the last element add to e *)

let rec exec s (e, le) code d nbi =
  match code with 
  | [] -> Printf.sprintf "%s" (let v = pop s
                               in begin 
                                    match v with 
                                    | CST k -> string_of_int k
                                    | _ -> ""
                                  end)
  | instr::c ->
    begin
    print_endline @@ print_instr instr ;
    print_endline @@ print_stack s ;
    match instr with
    | C k -> (push (CST k) s ; exec s (e, le) c d (nbi + 1))

    | REF k -> (push (SREF k) s; exec s (e, le) c d (nbi + 1)) 

    | BANG x ->
        let EnvREF k = Env.get_most_recent e x in begin push (CST !k) s; exec s (e, le) c d (nbi + 1) end

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
                            exec s (e, le) c d (nbi + 1)
        | (SREF r, CST j) -> 
                               begin 
                                 push (CST j) s;
                                 r := j;
                                 exec s (e, le) c d (nbi + 1)
                               end
        end

    | ACCESS x -> 
        begin
        try 
        let o = Env.get_most_recent e x in
          begin 
              push (stack_of_env o) s ; 
              exec s (e, le) c d (nbi + 1)
          end
        with Not_found -> failwith ("var not in environment : " ^ (string_of_int nbi) ^ " instr executed") 
        end

    | CLOSURE (x, c') -> ( push (CLOS (x, c', e)) s ; exec s (e, le) c d (nbi + 1))

    | CLOSUREC (f, x, c') -> 
        let e' = Env.add e f (EnvCLOS (x, c', e)) in 
        begin
          push (CLOS (x, c', e')) s;
          exec s (e, le) c d (nbi + 1)
        end

    | APPLY ->
        let CST v = pop s in let CLOS (x, c', e') = pop s in 
        begin 
          push (ENV (e, le)) s; 
          push (CODE c) s;
          let e'' = Env.add e x (EnvCST v) in 
          exec s (e'', x) c' d  (nbi + 1) (* c' should end by a
          return which will resume the exec *)
        end
      (* just put e instead of e' in the add e x, we'll see though *)

    | RETURN -> 
        let v = pop s in 
        let CODE c' = pop s in 
        let  ENV (e', le') = pop s 
        in  
          push v s; 
          exec s (e', le') c' d  (nbi + 1)

    | PRINTIN -> 
        let v = pop s in
        begin
          match v with
          | CST k -> begin print_int k ; print_string "\n" ; push v s ; exec s (e, le) c d  (nbi + 1) end
          | _ -> failwith "can't printin else than CST int"
        end

    | LET x -> 
        let v = pop s in
        begin match v with
        | _ ->
        let e' = Env.add e x (env_of_stack v) in
          push (e, le) d ; 
          exec s (e', x) c d  (nbi + 1)
        end
    | ENDLET -> let (e', le') = pop d in exec s (e', le') c d  (nbi + 1)

    | PROG prog_code -> begin push (CODE prog_code) s ; exec s (e, le) c d (nbi + 1) end

    | BRANCH -> 
        let CODE b = pop s
        in let CODE a = pop s
        in let CST k = pop s
        in if k = 0 then exec s (e, le) (b @ c) d (nbi + 1)
           else exec s (e, le) (a @ c) d (nbi + 1)

    | _ -> failwith "not implemented "
        
end


let exec_wrap code = exec (Stack.create ()) (Env.create, "") code (Stack.create ()) 0

