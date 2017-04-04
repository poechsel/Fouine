open Expr
open Binop
open Env
open Stack
(* possible : compter les réfs vers les éléments de s et  et faire du garbage collecting *)

type instr = 
    C of int 
    | BOP of expr binOp 
    | ACCESS of string 
    | CLOSURE of string*code
    | LET of string
    | ENDLET
    | APPLY
    | RETURN
    | PRINTIN (* affiche le dernier élément sur la stack, ne la modifie pas *)
and code = instr list

type stack_items = CODE of code | CLOS of string*code*(int Env.t) | CST of int | ENV of (int Env.t)*string

let rec print_code code =
    match code with
        | [] -> ""
        | i::q -> print_instr i ^ print_code q

and print_instr i =
    match i with
        | C k -> Printf.sprintf "CONST(%s); " @@ string_of_int k
        | BOP bop -> bop # symbol ^ "; "
        | ACCESS s -> Printf.sprintf "ACCESS(%s); " s
        | CLOSURE (x, c) -> Printf.sprintf "CLOSURE(%s, %s); " x (print_code c)
        | LET x -> Printf.sprintf "LET %s; " x
        | ENDLET -> Printf.sprintf "ENDLET; "
        | RETURN -> Printf.sprintf "RETURN; "
        | APPLY -> Printf.sprintf "APPLY; "
        | PRINTIN -> Printf.sprintf "PRINTIN; "

let print_stack s = 
    let v = pop s in
    begin
        match v with
            | CODE c -> print_endline @@ print_code c
            | CLOS (x, c, e) -> print_endline @@ "CLOS around " ^ x
            | CST k -> print_endline @@ "last element of stack is CST " ^ (string_of_int k)
            | ENV (e, le) -> print_endline @@ "ENV with last element " ^ le
       
    end ; push v s

let rec compile = function
    | Const k -> [C k]
    | Unit -> []
    | Ident (id, _) -> [ACCESS id]
    | BinOp (op, e1, e2, _) -> (compile e2) @ (compile e1) @ [BOP op] 
    | Fun (id, e, _) -> begin
                          match id with
                          | Ident(x, _) -> [CLOSURE (x, (compile e) @ [RETURN]) ]
                          | _ -> failwith "wrong identifier"
                        end
    | Let (a, b, _) -> 
      begin match a with
        | Ident(x, _) -> (compile a) @ [LET x] @ (compile b) @ [ENDLET] (* to do : remove only most recent x, have a copy of the old environment with eventually old x *)
        | _ -> failwith "bad let use"
      end
    | (Call(a,b, _) | Seq(a, b, _) | In(a, b, _)) -> begin
                    match a with
                        | Let(Ident(x, _), expr, _) -> (compile expr) @ [LET x] @ (compile b) @ [ENDLET] 
                        | _ -> (compile a) @ (compile b) @ [APPLY]
                  end 
    | Printin (Const k, _) -> [C k; PRINTIN]  (* assuming we only have cst for printin for the moment *)
    | _ -> failwith "compilation not implemented"


(* problem with env : the one of pierre uses keys, the one for secd machine sometimes looks more like a stack. so for let and endlet i don't know what to do yet *)
(* dans ma stack il y a :
*  - du code (instr list)
*  - des closures (e * code)
*  - des constantes *)
(* i'm now using dump to store old env during LET / ENDLET operations *)
(* until i implement bruijn substitution (or else), my closure have a string argument -> identifier *)


let new_id e =
let id = ref 1 in
while (Env.mem e (string_of_int !id)) do
incr id done;
string_of_int !id

(* le is the last element add to e *)

let rec exec s (e, le) code d =
  match code with 
  | [] -> Printf.sprintf "%s" (let CST k = pop s in string_of_int k)
  | instr::c ->
    begin
    match instr with
    | C k -> (push (CST k) s ; exec s (e, le) c d)
    | BOP binOp -> let n2, n1 = pop s, pop s in
                   begin 
                     match n1, n2 with
                     | (CST i, CST j) -> push (CST (let Const k = (binOp # act (Const i) (Const j)) in k)) s ; exec s (e, le) c d
                     | _ -> failwith "wrong type for binop operation"
                   end
    | ACCESS x -> let o = Env.get_most_recent e x in (push (CST o) s ; exec s (e, le) c d) (* to do : be able to store cst and closures in Env -> implement ACCESS(f) *) 
    | CLOSURE (x, c') -> ( push (CLOS (x, c', e)) s ; exec s (e, le) c d ) 
    | APPLY ->
      let CST v = pop s in let CLOS (x, c', e') = pop s in 
        begin 
          push (ENV (e, le)) s; 
          push (CODE c) s;
          let e' = Env.add e' x v in exec s (e', x) c' d (* c' should end by a
          return which will resume the exec *)
        end
    | RETURN -> let v = pop s in let CODE c' = pop s in let  ENV (e', le') = pop s in (push v s; exec s (e', le') c' d)
    | PRINTIN -> let v = pop s in
                 begin
                   match v with
                    | CST k -> begin print_int k ; print_string "\n" ; push v s ; exec s (e, le) c d end
                    | _ -> failwith "can't printin else than CST int"
                 end
    | LET x -> 
             let v = pop s in
             begin
               match v with
               | CST k ->
                   let e' = Env.add e x k in ( push (e, le) d ; exec s (e', x) c d )
               | CLOS (y, c', e') -> failwith "not implemented (func call)"                  
             end
    | ENDLET -> let (e', le') = pop d in exec s (e', le') c d
    | _ -> failwith "not implemented"
    end


let exec_wrap code = exec (Stack.create ()) (Env.create, "") code (Stack.create ())
