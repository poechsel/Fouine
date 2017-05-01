open Expr
open Binop

type instr =
    | C of int
    | BOP of (expr, type_listing) binOp
    | ACCESS of string
    | ACC of int (*specific de de bruijn *)
    | TAILAPPLY (* tail call optimization *)
(*    | UNITCLOSURE of code  *)
    | CLOSURE of code
    | CLOSUREC of code 
    | LET
    | ENDLET
    | APPLY
    | RETURN
    | PRINTIN (* affiche le dernier élément sur la stack, ne la modifie pas *)
    | BRANCH
    | PROG of code
    | REF
    | AMAKE
    | ARRITEM
    | ARRSET
    | BANG 
    | TRYWITH
    | EXIT
    | PASS
    (* specific instructions *)
    | PUSHMARK
    | GRAB

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
(*      | UNITCLOSURE (c) -> Printf.sprintf " UNICLOSURE(%s);" (print_code c)  *)
      | CLOSURE c -> Printf.sprintf " CLOSURE(%s);" (print_code c)
      | CLOSUREC c -> Printf.sprintf " CLOSUREC(%s);" (print_code c)
      | LET -> Printf.sprintf " LET;"
      | ENDLET -> Printf.sprintf " ENDLET;"
      | RETURN -> Printf.sprintf " RETURN;"
      | APPLY -> Printf.sprintf " APPLY;"
      | PRINTIN -> Printf.sprintf " PRINTIN;"
      | BRANCH -> Printf.sprintf " BRANCH;"
      | PROG c -> Printf.sprintf " PROG(%s);" (print_code c)
      | REF -> Printf.sprintf " REF;"
      | BANG -> Printf.sprintf " BANG;"
      | EXIT -> Printf.sprintf " EXIT;"
      | ARRITEM -> Printf.sprintf " ARRITEM;"
      | ARRSET -> Printf.sprintf "ARRSET; "
      | _ -> Printf.sprintf "not implemented;"

