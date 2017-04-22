open Expr
open Binop
open Env
open Dream
open Stack
open Prettyprint

type instr =
    C of int
    | BOP of (expr, type_listing) binOp
    | ACCESS of string
    | ACC of int
    | UNITCLOSURE of code
    | CLOSURE of code
    | CLOSUREC of string*string*code
    | LET
    | ENDLET
    | APPLY
    | RETURN
    | PRINTIN (* affiche le dernier élément sur la stack, ne la modifie pas *)
    | BRANCH
    | PROG of code
    | REF of int ref
    | AMAKE
    | ARRITEM
    | ARRSET
    | BANG of string
    | TRYWITH
    | EXIT
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
      | ACC i -> Printf.sprintf " ACC(%s);" (string_of_int i)
      | UNITCLOSURE (c) -> Printf.sprintf " UNICLOSURE(%s);" (print_code c)
      | CLOSURE c -> Printf.sprintf " CLOSURE(%s);" (print_code c)
      | CLOSUREC (x, x', c) -> Printf.sprintf " CLOSUREC(%s, %s, %s);" x x' (print_code c)
      | LET -> Printf.sprintf " LET;"
      | ENDLET -> Printf.sprintf " ENDLET;"
      | RETURN -> Printf.sprintf " RETURN;"
      | APPLY -> Printf.sprintf " APPLY;"
      | PRINTIN -> Printf.sprintf " PRINTIN;"
      | BRANCH -> Printf.sprintf " BRANCH;"
      | PROG c -> Printf.sprintf " PROG(%s);" (print_code c)
      | REF k -> Printf.sprintf " REF(%s);" (string_of_int !k)
      | BANG x -> Printf.sprintf " BANG %s;" x
      | EXIT -> Printf.sprintf " EXIT;"
      | ARRITEM -> Printf.sprintf " ARRITEM;"
      | ARRSET -> Printf.sprintf "ARRSET; "
      | _ -> Printf.sprintf "not implemented;"

let rec compile expr =
  begin 
    match expr with
    | Const k -> [C k]
    | BinOp (op, e1, e2, _) ->
        (compile e2) @
        (compile e1) @ [BOP op]
    | Access (n) -> [ACC n]
    | Lambda (a) ->
        [CLOSURE ( (compile a) @ [RETURN] )]
    | Call (a, b, _) ->
        (compile a) @
        (compile b) @
        [APPLY]
    | Let (a, b, _) ->
        (compile a) @
        [LET] @
        (compile b) @
        [ENDLET]
    | Seq (a, b, _) -> 
        (compile a) @
        (compile b)
    | _ -> failwith (Printf.sprintf "compilation not implemented on %s" (pretty_print expr)) 
  end
      

