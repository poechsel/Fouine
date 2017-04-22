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
               | EnvCODE of code
and stack_items = CODE of code
                | CLOS of string*code*(env_items, type_listing) Env.t
                | UNITCLOS of code*(env_items, type_listing) Env.t
                | CST of int
                | ENV of ((env_items, type_listing) Env.t)
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
      | ENV (e) -> Printf.sprintf "ENV"
      | SREF r -> Printf.sprintf "REF of value : %s" (string_of_int !r)
      | ARR a -> Printf.sprintf "array "
      | _ -> ""
    end
    with Stack.Empty -> Printf.sprintf "stack is empty for the moment"

let stack_of_env o =
    match o with
    | EnvCST k -> CST k
    | EnvCLOS (x, c, e) -> CLOS (x, c, e)
    | EnvUNITCLOS (c, e) -> UNITCLOS (c, e)
    | EnvREF r -> SREF r
    | EnvARR a -> ARR a
    | EnvCODE c -> CODE c

let env_of_stack o =
    match o with
    | CST k -> EnvCST k
    | CLOS (x, c, e) -> EnvCLOS (x, c, e)
    | UNITCLOS (c, e) -> EnvUNITCLOS (c, e)
    | SREF r -> EnvREF r
    | ARR a -> EnvARR a
    | CODE c -> EnvCODE c
    | _ -> failwith "WRONG_CONVERSION_ENV_FROM_STACK"

let rec exec s e code d nbi debug =
  match code with
  | [] -> Printf.sprintf "- : %s" (let v = pop s
                               in begin
                                    match v with
                                    | CST k -> string_of_int k
                                    | CLOS (x, c, e) -> print_code c
                                    | _ -> "not found"
                                  end)
  | instr::c ->
    if debug then begin
    print_endline @@ Printf.sprintf "\n%s-th instruction" (string_of_int nbi);
    print_endline @@ print_instr instr ;
    print_endline @@ Printf.sprintf "next instructions : %s" (print_code c);
    print_endline @@ print_stack s end;
    match instr with
       


