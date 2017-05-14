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
   t : float}

(* shortcuts for improving readability of the printing functions *)
let pe = print_endline and pf = Printf.sprintf

let incr_exec exec_info = incr exec_info.nb_op

(* prints the element on top of the stack *)
let print_stack s =
    try
    let v = top s in
    "top of stack -> " ^
    begin
      match v with
      | CODE c -> pf "lines of code : %s" (print_code c false)
      | CLS (c, e) -> pf "CLOSURE of code %s " (print_code c false)
      | CLSREC (c, e) -> pf "CLSREC of some code, some env"
      | CST k -> pf "CST of %s" (string_of_int k)
      | BOOL b -> pf (if b then "true" else "false")
      | REF r -> pf "REF value"
      | ARR a -> pf "array "
      | TUPLE l -> pf "tuple of length %s" (string_of_int (List.length l))
      | _ -> ""
    end
    with Stack.Empty -> pf "stack is empty for the moment"
(* function printing debug informations *)
let print_debug s e c exec_info instr =
  begin
    pe @@ pf "\n%s-th instruction" (string_of_int !(exec_info.nb_op));
    pe @@ pf "env size: %s" (string_of_int @@ size e);
    pe @@ pf "items of the env %s" (DreamEnv.print_env e);
    pe @@ pf "next instructions:%s" (print_code c false);
    pe @@ print_stack s;
    pe @@ pf "stack size: %s" (string_of_int @@ length s);
    pe @@ print_instr instr
  end

(** END debugging **)


(* printing functions, called when computation is over *)

let print_array a =
  let n = Array.length a in
  let rec aux a k n =
    if k = n-1 then ""
    else (string_of_int a.(k)) ^ (aux a (k+1) n)
  in aux a 0 n

let print_item i =
  match i with
  | CST k -> string_of_int k
  | BOOL b -> if b then "true" else "false"
  | ARR a -> print_array a
  | (CLS (c, e) | CLSREC (c, e)) -> print_code c false
  | _ -> ""

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
      with _ -> "()"
  end


(** EXTRACTING FUNCTIONS / for items **)

let get_ref r =
  match r with
  | REF r -> r
  | _ -> raise RUNTIME_ERROR

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

let get_code c =
  match c with
  | CODE code -> code
  | _ -> raise RUNTIME_ERROR

let get_env v =
  match v with
  | ENV e -> e
  | _ -> raise RUNTIME_ERROR

let get_cst v = 
  match v with
  | CST k -> k
  | _ -> raise RUNTIME_ERROR

let get_arr v = 
  match v with
  | ARR a -> a
  | _ -> raise RUNTIME_ERROR

let get_cls v = 
  match v with
  | CLS (c, e) -> (c, e)
  | _ -> raise RUNTIME_ERROR

let get_tuple v =
  match v with
  | TUPLE l -> l
  | _ -> raise RUNTIME_ERROR

let pop_ref s = let v = pop s in get_ref v

let pop_cls s = let v = pop s in get_cls v

let pop_code s = let v = pop s in get_code v

let pop_env s = let v = pop s in get_env v

let pop_cst s = let v = pop s in get_cst v

let pop_arr s = let v = pop s in get_arr v

let pop_tuple s = let v = pop s in get_tuple v
