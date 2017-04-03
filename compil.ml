open Expr
open Binop
open Env
open Stack
(* possible : compter les réfs vers les éléments de s et  et faire du garbage collecting *)

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
        | BOP bop -> bop # symbol ^ "; "
        | ACCESS s -> Printf.sprintf "ACCESS(%s); " s
        | CLOSURE c -> Printf.sprintf "CLOSURE(%s); " (print_code c)
        | LET -> Printf.sprintf "LET; "
        | ENDLET -> Printf.sprintf "ENDLET; "
        | RETURN -> Printf.sprintf "RETURN; "
        | APPLY -> Printf.sprintf "APPLY; "
        | PRINTIN -> Printf.sprintf "PRINTIN; "

let rec compile = function
    | Const k -> [C k]
    | Unit -> []
    | Ident (id, _) -> [ACCESS id]
    | BinOp (op, e1, e2, _) -> (compile e2) @ (compile e1) @ [BOP op] 
    | Fun (id, e, _) -> begin
                          match id with
                          | Ident(x, _) -> [CLOSURE ((compile e) @ [RETURN]) ]
                          | _ -> failwith "wrong identifier"
                        end
    | Let (a, b, _) -> (compile a) @ [LET] @ (compile b) @ [ENDLET]
    | In(a, b, _) -> begin
                    match a with
                        | Let _ -> (compile a) @ [LET] @ (compile b) @ [ENDLET] 
                        | _ -> (compile a) @ (compile b) @ [APPLY]
                  end 
    | IfThenElse (cond, a, b, _) -> failwith "not implemented" 
    | Printin (Const k, _) -> [C k; PRINTIN]  (* assuming we only have cst for printin for the moment *)
    | _ -> failwith "not implemented"


(* problem with env : the one of pierre uses keys, the one for secd machine sometimes looks more like a stack. so for let and endlet i don't know what to do yet *)
(* dans ma stack il y a :
*  - du code (instr list)
*  - des closures (e * code)
*  - des constantes *)

type stack_items = CODE of code | CLOS of code*(int Env.t) | CST of int | ENV of (int Env.t)*string

let new_id e =
let id = ref 1 in
while (Env.mem e (string_of_int !id)) do
incr id done;
string_of_int !id

(* le is the last element add to e *)
let rec exec s (e, le) code  =
  match code with 
  | [] -> Printf.sprintf "last element in s : %s" @@ (let CST k = pop s in string_of_int k)
  | instr::c ->
    begin
    match instr with
    | C k -> (push (CST k) s ; exec s (e, le) c)
    | BOP binOp -> let n2, n1 = pop s, pop s in
                   begin 
                     match n1, n2 with
                     | (CST i, CST j) -> push (CST (let Const k = (binOp # act (Const i) (Const j)) in k)) s ; exec s (e, le) c
                     | _ -> failwith "wrong type for binop operation"
                   end
    | ACCESS x -> let o = Env.get_most_recent e x in (push (CST o) s ; exec s (e, le) c)
    | CLOSURE c' -> push (CLOS (c', e)) s; exec s (e, le) c
    | APPLY -> let CST v, CLOS (c', e') = pop s, pop s in 
               begin push (ENV (e, le)) s; push (CODE c) s;
                     let x = new_id e in
                        let e' = Env.add e' x v in exec s (e', x) c'
               end
    | RETURN -> let v, CODE c', ENV (e', le') = pop s, pop s, pop s in (push v s; exec s (e', le') c')
    | PRINTIN -> let v = pop s in
                 begin
                   match v with
                    | CST k -> begin print_int k ; print_string "\n" ; push v s ; exec s (e, le) c end
                    | _ -> failwith "can't printin else than CST int"
                 end
    | LET -> let x = new_id e in 
             let CST k = pop s in
             let e' = Env.add e x k in exec s (e', x) c
    | ENDLET -> let e' = Env.remove e le in exec s (e', "") c 
    | _ -> failwith "not implemented"
    end
