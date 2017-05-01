open Expr
open Binop

type instr =
    | C of int
    | BOP of (expr, type_listing) binOp
    | ACCESS of string
    | ACC of int (*specific to de bruijn *)
    | TAILAPPLY (* tail call optimization *)
(*    | UNITCLOSURE of code  *)
(*    | BUILTINCLOSURE of (items -> items) *)
    | CLOSURE of code
    | CLOSUREC of code 
    | BUILTIN of string 
    | LET
    | ENDLET
    | APPLY
    | BAPPLY
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
    | EXCATCH
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
      | BUILTIN x -> " BUILTIN " ^ x ^ ";"
      | LET -> " LET;"
      | ENDLET -> " ENDLET;"
      | RETURN -> " RETURN;"
      | APPLY -> " APPLY;"
      | TAILAPPLY -> " TAILAPPLY;"
      | PRINTIN -> " PRINTIN;"
      | BRANCH -> " BRANCH;"
      | PROG c -> Printf.sprintf " PROG(%s);" (print_code c)
      | REF -> " REF;"
      | BANG -> " BANG;"
      | EXIT -> " EXIT;"
      | ARRITEM -> " ARRITEM;"
      | ARRSET -> "ARRSET; "
      | TRYWITH -> "TRYWITH; "
      | _ -> Printf.sprintf "not implemented;"

