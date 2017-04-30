open Expr
open Binop
open Env
open Stack
open Isa
open Bruijn
open Dream
type instr =
  C of int
  | BOP of (expr, type_listing) binOp
  | ACCESS of string
  | LET of string
  | ENDLET
  | UNITCLOSURE of code
  | CLOSURE of string*code
  | PUSHMARK
  | TAILAPPLY
  | GRAB
  | ARRITEM 
  | ARRSET
  | ARRMAKE

and code = instr list

let rec print_code code =
    match code with
        | [] -> ""
        | i::q -> print_instr i ^ print_code q

and print_instr i =
    match i with
      | C k -> Printf.sprintf " CONST(%s);" @@ string_of_int k
      | BOP bop -> " " ^ bop # symbol ^ ";"
      | ACCESS s -> Printf.sprintf " ACCESS(%s);" s
      | UNITCLOSURE (c) -> Printf.sprintf " UNICLOSURE(%s);" (print_code c)
      | CLOSURE (x, c) -> Printf.sprintf " CLOSURE(%s, %s);" x (print_code c)
      | CLOSUREC (x, x', c) -> Printf.sprintf " CLOSUREC(%s, %s, %s);" x x' (print_code c) 
      | LET x -> Printf.sprintf " LET %s;" x
      | ENDLET -> Printf.sprintf " ENDLET;"
      | RETURN -> Printf.sprintf " RETURN;"
      | APPLY -> Printf.sprintf " APPLY;"
      | PRINTIN -> Printf.sprintf " PRINTIN;"
      | BRANCH -> Printf.sprintf " BRANCH;"
      | PROG c -> Printf.sprintf " PROG(%s);" (print_code c)
      | REF k -> Printf.sprintf " REF(%s);" (string_of_int !k)
      | ARRAY a -> Printf.sprintf " ARRAY;"
      | BANG x -> Printf.sprintf " BANG %s;" x
      | EXIT -> Printf.sprintf " EXIT;"
      | ARRITEM -> Printf.sprintf " ARRITEM;" 
      | ARRSET -> Printf.sprintf " ARRSET;"
      | GRAB x -> Printf.sprintf "GRAB %S" x
      | _ -> Printf.sprintf "not implemented;"

let rec tailcompile expr =
  begin
  match expr with
  | Call (a, b, _) ->  (chain [] b) @ (compile a) @ [TAILAPPLY] 
  | Fun(Ident(x, _), e, _) -> [GRAB x] @ (tailcompile e) 
  | Ident(x, _) -> [ACCESS x] @ [RETURN]
  | _ -> compile expr
  end

and chain acc expr =
  begin
  match expr with
  | Call (a, b) -> chain ((compile b) :: acc) a
  | Ident(x, _) -> [ACCESS x] @ [RETURN]
  | _ -> (compile expr) :: acc
  end

and 
and compile expr =
  begin 
  match expr with
  
  | Fun (id, e, _) -> 
      begin
      match id with
        | Ident(x, _) -> [CLOSURE (x, (tailcompile e))]
        | Underscore -> [UNITCLOSURE( (compile e) @ [RETURN] )]
        | Unit -> [UNITCLOSURE( (compile e) @ [RETURN] )]
        | _ -> failwith "wrong identifier"
      end

  | Call(a,b, _) -> 
      begin 
      match b with
      | Unit -> (compile a) @ [APPLY]
      | _ ->
      begin
        match a with
        | Let(Ident(x, _), expr, _) -> (compile expr) @ [LET x] @ (compile b) @ [ENDLET] 
        | LetRec(Ident(f, _), expr, _) -> (compile expr) @ [LET f] @ (compile b) @ [ENDLET]
        | Call (a', b', _) -> [PUSHMARK] @ (chain [] b') @ (compile a') @ [APPLY]
        | _ -> (compile a) @ (compile b) @ [APPLY]
      end 
      end

  | Const k -> [C k]
  
  | Bool b -> if b then [C 1] else [C 0]
  
  | Unit -> []

  | Ident (id, _) -> [ACCESS id]

  | Ref (Const k, _) -> let r = ref k in [REF r]

  | Bang(Ident(x, _), _) -> [BANG x]

  | BinOp (op, e1, e2, _) -> 
      (compile e2) @ 
      (compile e1) @ [BOP op] 

  | Let (Underscore, expr, _) -> compile expr

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

  | Seq(a, b, _) -> (compile a) @ (compile b)

  | In(a, b, _) -> 
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

(* hacky : if there's a raise inside compile a, it will put a CST on the stack, so we can use eqOp to check
* match case *)
  | TryWith(a, Const k, b, _) ->
      [PROG (compile a)] @
      [PROG ([C k] @ [BOP eqOp] @ [PROG (compile b)] @ [PROG [EXIT]] @ [BRANCH])] @
      [TRYWITH]

  | TryWith(a, id, b, _) ->
      [PROG (compile a)] @
      [PROG (compile b)] @
      [TRYWITH]

  | Raise(Const(k), _) ->
      [C k] @ [EXIT]

  | ArrayMake (Const k, _) -> [ARRAY k]
   
  | ArrayItem(a, expr, _) -> 
      (compile expr) @
      (compile a) @
      [ARRITEM]

  | ArraySet (a, expr, nvalue, _) ->
     (compile nvalue) @
     (compile expr) @
     (compile a) @
     [ARRSET]

  | _ -> failwith "compilation not implemented"
  end


