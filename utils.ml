open Expr
open Shared
open CompilB
open Stack
open Dream
open DreamEnv

exception EXIT_INSTRUCTION
exception RUNTIME_ERROR
exception MATCH_FAILURE

(** DEBUGGING ELEMENTS **)

type exec_info_structure =
  {debug : bool ref;
   nb_op : int ref;
   jit   : bool ref;
   t     : float}

(* shortcuts for improving readability of the printing functions *)
let pe = print_endline and pf = Printf.sprintf

let incr_exec exec_info = incr exec_info.nb_op

(* prints the element on top of the stack *)
let print_stack s =
  if is_empty s then "Stack is empty"
  else
    begin
    let contenu = ref "" in
    let r = create () in
    while not (is_empty s) do
      let v = pop s in 
      let _ = push v r in
      contenu := !contenu ^ " << " ^ 
      begin
        match v with
        | CODE c -> pf "Encapsulated code :%s" (print_code c false)
        | CLS (c, e) -> pf "Closure of code%s" (print_code c false)
        | CLSREC (c, e) -> pf "Recursive closure"
        | CST k -> pf "Cst of %s" (string_of_int k)
        | BOOL b -> pf (if b then "Boolean true" else "Boolean false")
        | REF r -> pf "Ref value"
        | ARR a -> print_array a
        | TUPLE l -> pf "Tuple of length %s" (string_of_int (List.length l))
        | VOID -> pf "Void value"
        | UNIT -> pf "Unit value"
        | MARK -> pf "Tuple mark"
        | ZDUM -> pf "Dummy value"
        | ZMARK -> pf "Zinc mark"
        | BUILTCLS _ -> pf "Builtin closure"
        | ENV _ -> pf "Environment"
      end
    done;
    while not (is_empty r) do
      let v = pop r in push v s
    done;
    !contenu
    end

(* function printing debug informations *)
let print_debug s e c exec_info instr =
  begin
    pe "============================================================";
    pe @@ pf "== %s-th instruction" (string_of_int !(exec_info.nb_op));
    pe @@ pf "== Environment size: %s" (string_of_int @@ size e);
    pe @@ pf "== Environment items: %s" (DreamEnv.print_env e);
    pe @@ pf "== Next instructions:%s" (print_code c false);
    pe @@ pf "== Stack size: %s" (string_of_int @@ length s);
    pe @@ "== Stack elements:" ^ (print_stack s);
    pe @@ "== Processing instruction:" ^ (let s = (print_instr instr) in String.sub s 0 ((String.length s)-1));
  end

(** END debugging **)


(* printing functions, called when computation is over *)

let rec print_item i =
  match i with
  | CST k -> string_of_int k
  | BOOL b -> if b then "true" else "false"
  | ARR a -> print_array a
  | (CLS (c, e) | CLSREC (c, e)) -> "fouine function of code :" ^ (print_code c false)
  | TUPLE l -> print_tuple l
  | UNIT -> "()"
  | _ -> failwith "zz"

and print_tuple  = function
  | [] -> ""
  | [x] -> "(" ^ (print_item x) ^ ")"
  | x :: xs ->
      let rec aux = function
        | [x] -> ", " ^ (print_item x) ^ ")"
        | x :: xs -> ", " ^ (print_item x) ^ " " ^ (aux xs)
      in "(" ^ (print_item x) ^ (aux xs) 

  (* prints the result of computation as well as the running time of the program
 * if the option is enabled *)
let print_out s e exec_info =
  let _ = if !(exec_info.debug) then print_endline @@ "\nRunning time : " ^ (string_of_float (Unix.gettimeofday () -. exec_info.t)) else ()
  in
  "- : " ^
  begin
    try print_item (pop s)
    with _ ->
      try print_item (DreamEnv.front e)
      with _ -> ""
  end


(** EXTRACTING FUNCTIONS / for items **)

let process_binop binOp n1 n2 =
  match n1, n2 with
  | (CST i, CST j) -> 
      (CST (let resu = (binOp # act (FInt i) (FInt j)) in
                     begin
                       match resu with
                       | FInt k -> k
                       | FBool b -> if b then 1 else 0
                       | _ -> raise RUNTIME_ERROR
                     end))
  | (REF r, _) ->  r := n2; n2
  | _ -> raise RUNTIME_ERROR

exception UNIT_VALUE

let get_ref r =
  match r with
  | REF r -> r
  | UNIT -> raise UNIT_VALUE
  | _ -> raise RUNTIME_ERROR

let get_code c =
  match c with
  | CODE code -> code
  | UNIT -> raise UNIT_VALUE
  | _ -> raise RUNTIME_ERROR

let get_env v =
  match v with
  | ENV e -> e
  | UNIT -> raise UNIT_VALUE
  | _ -> raise RUNTIME_ERROR

let get_cst v = 
  match v with
  | CST k -> k
  | UNIT -> raise UNIT_VALUE
  | _ -> raise RUNTIME_ERROR

let get_arr v = 
  match v with
  | ARR a -> a
  | UNIT -> raise UNIT_VALUE
  | _ -> raise RUNTIME_ERROR

let get_cls v = 
  match v with
  | CLS (c, e) -> (c, e)
  | UNIT -> raise UNIT_VALUE
  | _ -> raise RUNTIME_ERROR

let get_tuple v =
  match v with
  | TUPLE l -> l
  | UNIT -> raise UNIT_VALUE
  | _ -> raise RUNTIME_ERROR

let rec pop_ref s = let v = pop s in
                    try get_ref v
                  with UNIT_VALUE -> pop_ref s

let rec pop_cls s = let v = pop s in 
                    try get_cls v 
                    with UNIT_VALUE -> pop_cls s

let rec pop_code s = let v = pop s in 
                    try get_code v 
                    with UNIT_VALUE -> pop_code s

let rec pop_env s = let v = pop s in 
                    try get_env v 
                    with UNIT_VALUE -> pop_env s

let rec pop_cst s = let v = pop s in 
                    try get_cst v 
                    with UNIT_VALUE -> pop_cst s

let rec pop_arr s = let v = pop s in try get_arr v 
                    with UNIT_VALUE -> pop_arr s

let rec pop_tuple s = let v = pop s in try get_tuple v 
                      with UNIT_VALUE -> pop_tuple s
