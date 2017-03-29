open Expr
open Binop
open Env

type instr = 
    C of int 
    | BOP of expr binOp 
    | ACCESS of string 
    | CLOSURE of code
    | LET
    | ENDLET
    | APPLY
    | RETURN
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
    | BinOp (op, e1, e2) -> (compile e2) @ (compile e1) @ [BOP op] 
    | Ident id -> [ACCESS id]
    | Fun (id, e) -> [CLOSURE ( (compile e) @ [RETURN] )]
    | Let (a, b) -> (compile a) @ [LET] @ (compile b) @ [ENDLET]
    | In(a, b) -> begin
                    match a with
                        | Let (_, _) -> (compile a) @ [LET] @ (compile b) @ [ENDLET] 
                        | _ -> (compile a) @ (compile b) @ [APPLY]
                  end 
    | _ -> failwith "not implemented"

let e2 = In(Const 1, Const 2)

