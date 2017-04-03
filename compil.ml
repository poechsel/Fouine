open Expr
open Binop
open Env
open Stack
(* possible : compter les réfs vers les éléments de s et  et faire du garbage collecting *)

type instr = 
    C of int 
    | BOP of expr binOp 
    | ACCESS of string 
    | CLOS of string*code
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
        | BOP bop -> bop # symbol ^ "; "
        | ACCESS s -> Printf.sprintf "ACCESS(%s); " s
        | CLOS (s, c) -> Printf.sprintf "CLOSURE(%s, %s); " s (print_code c)
        | LET -> Printf.sprintf "LET; "
        | ENDLET -> Printf.sprintf "ENDLET; "
        | RETURN -> Printf.sprintf "RETURN; "
        | APPLY -> Printf.sprintf "APPLY; "
        | PRINTIN -> Printf.sprintf "PRINTIN; "

let rec compile = function
    | Const k -> [C k]
    | Unit -> []
    | Ident id -> [ACCESS id]
    | BinOp (op, e1, e2, _) -> (compile e2) @ (compile e1) @ [BOP op] 
    | Fun (id, e, _) -> begin
                          match id with
                          | Ident(x) -> [CLOS (x, (compile e) @ [RETURN] )]
                          | _ -> failwith "wrong identifier"
                        end
    | Let (a, b, _) -> (compile a) @ [LET] @ (compile b) @ [ENDLET]
    | In(a, b, _) -> begin
                    match a with
                        | Let _ -> (compile a) @ [LET] @ (compile b) @ [ENDLET] 
                        | _ -> (compile a) @ (compile b) @ [APPLY]
                  end 
    | IfThenElse (cond, a, b, _) -> failwith "not implemented" 
    | Printin (expr, _) -> [CLOSURE (compile expr)] @ [APPLY] @ [PRINTIN] 
    | _ -> failwith "not implemented"

let e2 = In(Const 1, Const 2, Lexing.dummy_pos)

(* problem with env : the one of pierre uses keys, the one for secd machine sometimes looks more like a stack. so for let and endlet i don't know what to do yet *)
(* all code must take into account we can modify the code to be executed next with RETURN *)
(* dans ma stack il y a :
*  - du code (instr list)
*  - des closures (e * code)
*  - des constantes *)

type stack_items = Code of code | CLOS of string*code*(int Env.t) | Cst of int


let rec exec s e code  =
    match code with 
    | [] -> Printf.sprintf "last element in s : %s" @@ string_of_int (pop stack)
    | instr::c ->
        begin
        match instr with
        | C k -> push (Cst k) s ; exec s e c
        | BOP binOp -> let n2, n1 = pop stack, pop s in
                       begin 
                         match n1, n2 with
                         | (C i, C j) -> push ( C (i binOp j) ) s ; exec s e c
                         | failwith "wrong type for binop operation"
                       end
        | ACCESS x -> begin 
                        let o = Env.get_most_recent e x in push o s ;
                        stack, e, c
                      end
        | CLOS (x, c') -> push (Clos (x, c', e)) stack; exec s e c
        | APPLY -> let Clos(x, c', e'), v = pop stack, pop s in 
                   begin
                     push e stack;
                     push c stack;
                     let e' = Env.add e' x v in exec s e' c'
                   end
        | RET -> let v, c', e' = pop stack, pop stack, pop s in 
                 begin
                   push v s;
                   exec s e' c'
                 end
        | PRINTIN -> let v = pop s in 
                     begin
                       match v with
                        | Const k -> begin
                                       Printf.sprintf "%s" (string_of_int k) ;
                                       push v s ;
                                       exec s e c
                                     end
                        | _ -> failwith "can't printin else than Const int"
                     end
        (*| LET -> *) 
        (* | ENDLET -> e.pop *) (* e must be a s *)
        | _ -> failwith "not implemented"
