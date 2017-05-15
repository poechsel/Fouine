open Binop 
open Errors

let int_of_bool b =
  if b then 1 else 0
let bool_of_int b =
  if b = 0 then false else true

type identifier = string list * string


let string_of_ident (l, n) =
   List.fold_left (fun a b -> a ^ b ^ "." )  "" l ^ n



type 'a perhaps =
  | None
  | Some of 'a


module Types =  struct
  (* structure for types *)
  type types =
    | Int
    | Bool
    | Array of types
    | Unit
    | Var of tv ref
    | Ref of types
    | Fun of types * types
    | Tuple of types list
    | Constructor of identifier * types * types perhaps (* a constructor has a name, a father, and a type *)

    | Generic    of int
    | Polymorphic    of string (*for a polymoric type *)
    | Called         of identifier * int * types list (* for types like ('a, 'b) expr *)

  and tv = Unbound of int * int | Link of types



type user_defined =
  | Renamed_decl of types
  | Sum_decl    of types
  | Constructor_decl of types 
  | Module_sig_decl of module_type_listing list
and declaration =
  | Constructor_list of types list
  | Basic of types
  | Module of module_type_listing list


and module_type_listing =
  | Val_entry of identifier * types
  | Type_entry of types * types perhaps

type module_signature = 
  | Register of identifier
  | Unregister of module_type_listing list



  type sum =
    | CType_cst of string 
    | CType       of string * types


  (* dealing with polymorphic types. We want every newly created to be different from the previous one *)
  let current_pol_type = ref 0
  (* get the next id corresponding to a polymorphic type *)
  let new_generic_id () =
    let _ = incr current_pol_type 
    in !current_pol_type
  (* new variable *)
  let new_var level = 
    Var (ref (Unbound (new_generic_id (), level)))

  let new_generic () = 
    Generic (new_generic_id ())


  let is_atomic t =
    match t with
    | Tuple _ | Fun _ -> false
    | _ -> true

  let print_polymorphic tbl y =
    if not (Hashtbl.mem tbl y) then 
      Hashtbl.add tbl y (Hashtbl.length tbl); 
    let id = Hashtbl.find tbl y
    in let c = (Char.chr (Char.code 'a' + id mod 26)) 
    in if id > 26 then
      Printf.sprintf "%c%d" c (id / 26)
    else 
      Printf.sprintf "%d" y 

  let pretty_print_aux t tbl = 
    let rec add_parenthesis a = 
      if is_atomic a then aux a
      else "("^aux a^")"
    and aux t=
      match t with
      | Int -> "int"
      | Bool -> "bool"
      | Array x -> aux x ^ " array"
      | Ref x -> Printf.sprintf "ref %s" (aux x)
      | Unit -> "unit"
      | Var x -> begin
          match (!x) with
          | Unbound (y, _) ->                      (* a bit long, because we are trying to mimic the formating of caml *)
            "'_"^print_polymorphic tbl y
          | Link l -> aux l
        end
      | Generic y ->
        "gen '" ^ print_polymorphic tbl y
      | Fun (a, b) ->  
        Printf.sprintf ("%s -> %s") (add_parenthesis a) (aux b)
      | Tuple l -> 
        List.fold_left (fun a b ->  a ^ " * " ^ (add_parenthesis b)) (add_parenthesis @@ List.hd l) (List.tl l)
      | Constructor (name, father, Some t) ->
        Printf.sprintf "%s of (%s)" (string_of_ident name)  (add_parenthesis t) 
      | Constructor(name, father, None) ->
        Printf.sprintf "%s" (string_of_ident name)
      | Polymorphic l -> "["^l^"]"
      | Called (name, i, params) ->
        if params = [] then
          string_of_ident name ^ " : " ^ string_of_int i
        else 
          let temp =
            List.fold_left (fun a b -> a ^ ", " ^ (add_parenthesis b)) (add_parenthesis @@ List.hd params) (List.tl params)
          in if List.length params = 1 then
            Printf.sprintf "%s %s" temp (string_of_ident name)
          else
            Printf.sprintf "%s %s" temp (string_of_ident name)
    in aux t

  (* print a type *)
  let rec print t = 
    let tbl = Hashtbl.create 1 in
    pretty_print_aux t tbl

  (* print two types will keeping the same table for polymorphic vars *)
  let rec print_duo t1 t2 =
    let tbl = Hashtbl.create 1 in
    Printf.sprintf "%s, %s" (pretty_print_aux t1 tbl) (pretty_print_aux t2 tbl)


end



(* our ast *)
type 'a expr = 
  | Open of string * Lexing.position
  | Constructor of identifier * 'a expr perhaps * Lexing.position (* a type represeting a construction in the form Constructor (name,parent, value) *)
  | TypeDecl of Types.types * Types.declaration * Lexing.position
  | FixedType of 'a expr * Types.types * Lexing.position
  | Eol
  | Const     of int
  | Bool      of bool
  | Underscore 
  | ArrayItem of 'a expr * 'a expr * Lexing.position
  | ArraySet  of 'a expr * 'a expr * 'a expr * Lexing.position
  | Ident       of identifier * Lexing.position
  | Seq of 'a expr * 'a expr * Lexing.position
  | Unit
  | Not       of 'a expr * Lexing.position
  | In        of 'a expr * 'a expr * Lexing.position
  | MainSeq of 'a expr * 'a expr * Lexing.position (* this token is here uniquely to deal with file loading. It acts exactly like a seq *)
  | Let       of 'a expr * 'a expr  * Lexing.position
  | LetRec       of 'a expr * 'a expr * Lexing.position
  | Call      of 'a expr * 'a expr * Lexing.position
  | TryWith of 'a expr * 'a expr * 'a expr * Lexing.position
  | Raise of 'a expr * Lexing.position
  | Bang of 'a expr * Lexing.position
  | Ref of 'a expr * Lexing.position
  | IfThenElse of 'a expr * 'a expr * 'a expr * Lexing.position
  | RefLet of 'a expr * 'a expr * Lexing.position
  | Fun of 'a expr * 'a expr * Lexing.position
  | Printin of 'a expr * Lexing.position
  | ArrayMake of 'a expr * Lexing.position
  | BinOp of ('a, Types.types) binOp * 'a expr * 'a expr * Lexing.position
  | Tuple of 'a expr list * Lexing.position
  | MatchWith of 'a expr * ('a expr * 'a expr) list * Lexing.position
  | Module of string * 'a expr list * Types.module_signature perhaps * Lexing.position
  | Value of 'a



  (* used for de bruijn indices preprocess *)
  | Access of int
  | Lambda of 'a expr
  | LambdaR of 'a expr
  | LetIn of 'a expr * 'a expr
  | LetRecIn of 'a expr * 'a expr
  | Bclosure of ('a code Dream.DreamEnv.item -> 'a code Dream.DreamEnv.item)
  | LetTup of 'a expr * 'a expr  (* could use Let instead of this, but less understandable *)
  | LetInTup of 'a expr * 'a expr * 'a expr (* really need for now because of compilB specifics *)

(** SET OF INSTRUCTIONS FOR THE SECD AND ZINC MACHINES **)

and 'a instr =
  | C of int
  | B of bool
  | BOP of ('a, Types.types) binOp
  | ACCESS of string
  | ACC of int (*specific to de bruijn *)
  | TAILAPPLY (* tail call optimization *)
  | CLOSURE of 'a code
  | CLOSUREC of 'a code 
  | BUILTIN of ('a code Dream.DreamEnv.item -> 'a code Dream.DreamEnv.item)
  | LET
  | ENDLET
  | APPLY
  | RETURN
  | PRINTIN (* affiche le dernier élément sur la stack, ne la modifie pas *)
  | BRANCH
  | PROG of 'a code
  | REF
  | AMAKE
  | ARRITEM
  | ARRSET
  | BANG 
  | TRYWITH
  | EXIT
  | PASS
  | EXCATCH
  | UNIT
  | DUPL
  | SWAP
  | MATCH of int
  | PUSHMARK
  | UNFOLD
  | CONS
  (* ZINC SPECIFIC INSTRUCTIONS : UNUSED BY SECD MACHINE *)
  | GRAB
  | APPTERM
  | CUR of 'a code
  | DUMMY
  | UPDATE
  | PUSH

and 'a code = 'a instr list

(* manipulating ast in secd *)

let is_tup a = match a with
  | Tuple _ -> true
  | _ -> false

  let extr_tup a = match a with
  | Tuple (l, _) -> l
  | _ -> failwith "Expression is not a tuple."

let ident_equal i j =
  match (i, j) with
  | Ident(a, _), Ident(b, _) when a = b -> true
  | _ -> false


(* printing functions *)

let rec print_code code line_jump =
  match code with
  | [] -> ""
  | [i] -> let s = print_instr i in String.sub s 0 ((String.length s) -1)
  | i::q -> print_instr i ^ (if line_jump then "\n" else "") ^ print_code q line_jump

and print_instr i =
  match i with
  | C k -> Printf.sprintf " CONST(%s);" @@ string_of_int k
  | BOP bop -> " " ^ bop # symbol ^ ";"
  | ACCESS s -> Printf.sprintf " ACCESS(%s);" s
  | ACC i -> Printf.sprintf " ACC(%s);" (string_of_int i)
  | CLOSURE c -> Printf.sprintf " CLOSURE(%s);" (print_code c false)
  | CLOSUREC c -> Printf.sprintf " CLOSUREC(%s);" (print_code c false)
  | BUILTIN x -> " BUILTIN " ^ ";"
  | LET -> " LET;"
  | ENDLET -> " ENDLET;"
  | RETURN -> " RETURN;"
  | APPLY -> " APPLY;"
  | TAILAPPLY -> " TAILAPPLY;"
  | PRINTIN -> " PRINTIN;"
  | BRANCH -> " BRANCH;"
  | PROG c -> Printf.sprintf " PROG(%s);" (print_code c false)
  | REF -> " REF;"
  | BANG -> " BANG;"
  | EXIT -> " EXIT;"
  | ARRITEM -> " ARRITEM;"
  | ARRSET -> " ARRSET;"
  | TRYWITH -> " TRYWITH;"
  | UNIT -> " UNIT;"
  | PASS -> " PASS;"
  | PUSHMARK -> " PUSHMARK;"
  | CONS -> " CONS;"
  | UNFOLD -> " UNFOLD;"
  | AMAKE -> " AMAKE;"
  | EXCATCH -> " EXCATCH;"
  | DUPL -> " DUPL;"
  | SWAP -> " SWAP;"
  | GRAB -> " GRAB;"
  | APPTERM -> " APPTERM;"
  | DUMMY -> " DUMMY;"
  | UPDATE -> " UPDATE;"
  | PUSH -> " PUSH;"
  | B b -> if b then " BOOL true;" else " BOOL false;"
  | MATCH i -> " MATCH;" ^ (string_of_int i)
  | CUR c -> Printf.sprintf " CUR(%s);" (print_code c false)



let get_operator_name node =
  match node with
  | Call(Call(Ident((l, n), _), _, _), _, _) when is_infix_operator n -> string_of_ident (l, n)
  | Call(Ident((l, n), _), _, _) when is_prefix_operator n -> string_of_ident (l, n)
  | _ -> ""


let is_node_operator node =
  match node with
  | Call(Call(Ident((_, n), _), _, _), _, _) when is_infix_operator n -> true
  | Call(Ident((_, n), _), _, _) when is_prefix_operator n -> true
  | _ -> false

(* interpretation function and type of an arithmetic operation *)



(* return true if expr is an 'atomic' expression *)
let is_atomic expr =
  match expr with
  | Bool _| Ident _ | Underscore | Const _ | Unit -> true
  | _ -> false

let rec show_expr e =
  match e with
  | Open _ -> "open"
  | Eol -> "eol"
  | Const _ -> "const"
  | Bool _ -> "bool"
  | Underscore -> "underscore"
  | ArrayItem _ -> "array item"
  | ArraySet _ -> "arr set"
  | Ident _ -> "ident"
  | Seq _ -> "seq"
  | Unit -> "unit"
  | Not _ -> "not"
  | In (a, b, _) -> Printf.sprintf "In (%s, %s)" (show_expr a) (show_expr b)
  | MainSeq _ -> "mainseq"
  | Let (a, b, _) -> Printf.sprintf "Let (%s, %s)" (show_expr a) (show_expr b)
  | LetRec _ -> "letrec"
  | Call (a, b, _) -> Printf.sprintf "Call (%s, %s)" (show_expr a) (show_expr b)
  | TryWith _ -> "trywwith"
  | Raise _ -> "raise"
  | Bang _ -> "bang"
  | Ref _ -> "ref"
  | IfThenElse _ -> "ifthenelse"
  | RefLet _ -> "reflet"
  | Fun _ -> "fun"
  | Printin _ -> "printin"
  | ArrayMake _ -> "arraymake"
  | BinOp _ -> "binop"
  | Tuple (l, _) -> Printf.sprintf "Tuple [%s]" (List.fold_left (fun a b -> a ^ "; " ^ (show_expr b)) "" l) 
  | Access _ -> "access"
  | Lambda _ -> "lambda"
  | LambdaR _ -> "lambdaR"
  | LetIn _ -> "letin"
  | LetRecIn _-> "letrecin"
  | TypeDecl _ -> "type decl"
  | Module _ -> "module"
  | LetInTup _ -> "LetInTup"
  | LetTup _ -> "LetTup"
  | Bclosure _ -> "Bclosure"
