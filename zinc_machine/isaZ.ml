open Expr
open Binop

type ('a, 'b) instr_Z =
    | C of int
    | BOP of ('a, type_listing) binOp
    | ACCESS of string
    | ACC of int (*specific de de bruijn *)
    | TAILAPPLY (* tail call optimization *)
    | CLOSURE of ('a, 'b) code_Z
    | CLOSUREC of ('a, 'b) code_Z
    | BUILTIN of ('b -> 'b)
    | LET
    | ENDLET
    | APPLY
    | RETURN
    | PRINTIN (* affiche le dernier élément sur la stack, ne la modifie pas *)
    | BRANCH
    | PROG of ('a, 'b) code_Z
    | REF
    | AMAKE
    | ARRITEM
    | ARRSET
    | BANG 
    | TRYWITH
    | EXIT
    | PASS
    | EXCATCH
    (* specific ZAM instructions *)
    | PUSHMARK
    | GRAB
    | APPTERM
    | CUR of ('a, 'b) code_Z (* cur is a cheap instruction used to simply put some code into the accu *)
    | DUMMY (* value used to evaluate recursive definitions *)
    | UPDATE (* physical upgrade of the dummy value in rec expression *)
    (* maybe rather loop in the code as before than do this *)
    | PUSH

and ('a, 'b) code_Z = ('a, 'b) instr_Z list

let rec print_code_Z code =
    match code with
        | [] -> ""
        | i::q -> print_instr i ^ print_code_Z q

and print_instr i =
    match i with
      | C k -> Printf.sprintf "CONST (%s); " @@ string_of_int k
      | BOP bop -> bop # symbol ^ "; "
      | ACCESS s -> Printf.sprintf "ACCESS (%s); " s
      | ACC i -> Printf.sprintf "ACC (%s); " (string_of_int i)
(*      | UNITCLOSURE (c) -> Printf.sprintf " UNICLOSURE(%s);" (print_code_Z c)  *)
      | CLOSURE c -> Printf.sprintf "CLOSURE (%s); " (print_code_Z c)
      | CLOSUREC c -> Printf.sprintf "CLOSUREC (%s); " (print_code_Z c)
      | LET -> "LET; "
      | ENDLET -> "ENDLET; "
      | RETURN -> "RETURN; "
      | APPLY -> "APPLY; "
      | PRINTIN -> "PRINTIN; "
      | BRANCH -> "BRANCH; "
      | PROG c -> Printf.sprintf "PROG(%s); " (print_code_Z c)
      | REF -> "REF; "
      | BANG -> "BANG; "
      | EXIT -> "EXIT; "
      | ARRITEM -> " ARRITEM; "
      | ARRSET -> "ARRSET; "
      | DUMMY -> "DUMMY; "
      | UPDATE -> "UPDATE; "
      | PUSH -> "PUSH; "
      | EXCATCH -> "EXCATCH; "
      | PUSHMARK -> "PUSHMARK; "
      | GRAB -> "GRAB; "
      | APPTERM -> "APPTERM; "
      | CUR c -> Printf.sprintf "CUR (%s); " (print_code_Z c)
      | _ -> "not implemented;"

