open Expr
open Binop
open Env

(* possible : compter les réfs vers les éléments de stack et dump et faire du garbage collecting *)

type instr = 
    C of int 
    | BOP of expr binOp 
    | ACCESS of string 
    | CLOSURE of code
    | LET
    | ENDLET
    | APPLY
    | RETURN
    | PRINTIN (* affiche le dernier élément sur la stack, ne la modifie pas *)
and code = instr list

let rec print_code code =
    match code with
        | [] -> ""
        | i::q -> print_instr i ^ print_code q

and print_instr i =
    match i with
        | C k -> Printf.sprintf "CONST(%s); " @@ string_of_int k
        | BOP bop -> bop # symbol
        | ACCESS s -> Printf.sprintf "ACCESS(%s); " s
        | CLOSURE c -> Printf.sprintf "CLOSURE(%s); APPLY" @@ print_code c
        | LET -> Printf.sprintf "LET; "
        | ENDLET -> Printf.sprintf "ENDLET; "
        | RETURN -> Printf.sprintf "RETURN; "
        | APPLY -> Printf.sprintf "APPLY; "

let rec compile = function
    | Const k -> [C k]
    | Unit -> []
    | Ident id -> [ACCESS id]
    | BinOp (op, e1, e2, _) -> (compile e2) @ (compile e1) @ [BOP op] 
    | Let (a, b, _) -> (compile a) @ [LET] @ (compile b) @ [ENDLET]
    | In(a, b, _) -> begin
                    match a with
                        | Let (_, _, _) -> (compile a) @ [LET] @ (compile b) @ [ENDLET] 
                        | _ -> (compile a) @ (compile b) @ [APPLY]
                  end 
    | Fun (id, e, _) -> [CLOSURE ( (compile e) @ [RETURN] )]
    | IfThenElse (cond, a, b, _) -> 
    | Printin (expr, _) -> [CLOSURE (compile expr)] @ [APPLY] @ [PRINTIN]
    |  
    | _ -> failwith "not implemented"

let e2 = In(Const 1, Const 2, Lexing.dummy_pos)

(* problem with env : the one of pierre uses keys, the one for secd machine is more like a stack. so.. stack ? *)
(* all code must take into account we can modify the code to be executed next with RETURN *)

(*
let rec exec code dump stack env =
    match code with 
    | [] -> [] dump stack env
    | x::xs -> exec_instr x dump stack env ; exec xs dump stack env

and exec_instr i dump stack env =
    match i with
    | C k -> stack.push k
    | BOP binOp -> let u, v = stack.pop, stack.pop in stack.push @@ u binOp v (* assuming u, v are integers ... *)
    | ACCESS x -> let o = Env.get_most_recent env x in (* assuming (for the moment) it's only int in env *) 
                  stack.push o
    | CLOSURE of c -> failwith "not implemented" (* make a copy of the env, push it on the stack c[e] *)
    (* | APPLY -> ?????? pop code, execute it in old env, but how to do that properly ??????? *)
    (* | LET -> let elem = stack.pop in Env.add env //what_key ? maybe brunjin indices// elem *)
    (* | ENDLET -> env.pop *) (* env must be a stack *)
    | RETURN -> let v = stack.pop in 
*) 
