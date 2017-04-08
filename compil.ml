open Expr
open Binop
open Env
open Stack
(* possible : compter les réfs vers les éléments de s et  et faire du garbage collecting *)

type instr = 
    C of int 
    | BOP of (expr, type_listing) binOp 
    | ACCESS of string 
    | CLOSURE of string*code
    | CLOSUREC of string*string*code
    | LET of string
    | ENDLET
    | APPLY
    | RETURN
    | PRINTIN (* affiche le dernier élément sur la stack, ne la modifie pas *)
    | BRANCH
    | PROG of code
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
      | CLOSURE (x, c) -> Printf.sprintf "CLOSURE(%s, %s); " x (print_code c)
      | CLOSUREC (x, x', c) -> Printf.sprintf "CLOSUREC(%s, %s, %s); " x x' (print_code c) 
      | LET x -> Printf.sprintf "LET %s; " x
      | ENDLET -> Printf.sprintf "ENDLET; "
      | RETURN -> Printf.sprintf "RETURN; "
      | APPLY -> Printf.sprintf "APPLY; "
      | PRINTIN -> Printf.sprintf "PRINTIN; "
      | BRANCH -> Printf.sprintf "BRANCH; "
      | PROG c -> Printf.sprintf "PROG (%s); " (print_code c)


let rec compile expr =
  begin
  print_endline @@ beautyfullprint expr ;
  match expr with 
  | Const k -> [C k]
  
  | Bool b -> if b then [C 1] else [C 0]

  | Unit -> []

  | Ident (id, _) -> [ACCESS id]

  | BinOp (op, e1, e2, _) -> 
      (compile e2) @ 
      (compile e1) @ [BOP op] 

  | Fun (id, e, _) -> 
      begin
      match id with
        | Ident(x, _) -> [CLOSURE (x, (compile e) @ [RETURN]) ]
        | _ -> failwith "wrong identifier"
      end

  | Let (Ident(x, _), expr, _) -> 
      (compile expr) @ 
      [LET x] @ [ACCESS x] 
      (* to do : remove only most recent x, have a copy of the old environment with eventually old x *)

  | LetRec (Ident(f, _), b, _) -> 
      begin 
        match b with
        | Fun(Ident(x, _), expr, _) -> [CLOSUREC(f, x, (compile expr) @ [RETURN])]
        | _ -> failwith "let rec must define a function"
      end

  | (Call(a,b, _) | Seq(a, b, _) | In(a, b, _)) -> 
      begin
        match a with
        | Let(Ident(x, _), expr, _) -> (compile expr) @ [LET x] @ (compile b) @ [ENDLET] 
        | LetRec(Ident(f, _), expr, _) -> (compile expr) @ [LET f] @ (compile b) @ [ENDLET]
        | _ -> (compile a) @ (compile b) @ [APPLY]
      end 

  | Printin (a, _) -> (compile a) @ [PRINTIN]  (* assuming we only have cst for printin for the moment *)

  | IfThenElse(cond, a, b, _) -> 
      (compile cond) @ 
      [PROG (compile a)] @ 
      [PROG (compile b)] @ [BRANCH]

  | _ -> failwith "compilation not implemented"
  end

