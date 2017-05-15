(* lib for dream environment for all compilation machine and Bruijn pre-process *)
open Array
open Binop

(* builtin functions --> l.48 *)

(* fonction mem sur des array *)
let mem a l =
  let rec aux i =
    if i = Array.length l then
      false
    else 
    if l.(i) = a then true
    else aux (i+1)
  in aux 0

let print_array a =
  let rec aux a k n =
    if k = n-1 then (string_of_int a.(k)) ^ "|]"
    else (string_of_int a.(k)) ^ "; " ^ (aux a (k+1) n)
  in "[|" ^ (aux a 0 (Array.length a))

(* MODULE DreamEnv *)
(* Utilisé par la SECD *)

module DreamEnv =
struct

  type 'a item =
    | CST of int
    | BOOL of bool
    | CLS of 'a * 'a dream
    | CLSREC of 'a * 'a dream
    | BUILTCLS of ('a item -> 'a item) 
    | REF of 'a item ref
    | ARR of int array
    | VOID
    | CODE of 'a
    | ENV of 'a dream
    | UNIT
    | PASS
    | MARK
    | TUPLE of ('a item list)
    | DUM
    (** ZINC SPECIFIC STACK ITEMS : UNUSED BY SECD **)
    | ZDUM
    | ZMARK
  
    (* dream est le type de l'environnement *)
  and 'a dream = {mutable ssize:int ; mutable size:int ; mutable arr:('a item array) ; mutable start:int }

  let rec dream_item_equal a b =
    match a, b with
    | CST a, CST b -> a = b
    | VOID, VOID -> true
    | UNIT, UNIT -> true
    | MARK, MARK -> true
    | ARR a, ARR b -> a = b
    | TUPLE l, TUPLE l' when List.length l = List.length l' ->
      List.for_all2 dream_item_equal l l'
    | _ -> false
  let rec dream_item_slt a b =
    match a, b with
    | CST a, CST b -> a < b
    | VOID, VOID -> false
    | UNIT, UNIT -> false
    | MARK, MARK -> false
    | ARR a, ARR b -> a < b
    | TUPLE l, TUPLE l' when List.length l = List.length l' ->
    let rec aux l l' = 
      match (l, l') with
      | x::tl, y::tl' when dream_item_equal x y -> aux tl tl'
      | x::tl, y::tl' when dream_item_slt x y -> true
      | _ -> false
    in aux l l'
    | _ -> false

  let dream_item_slt_or_equal a b  = dream_item_equal a b || dream_item_slt a b
  let dream_item_nequal a b = not (dream_item_equal a b)
  let dream_item_glt a b = not (dream_item_slt_or_equal a b) 
  let dream_item_glt_or_equal a b = not (dream_item_slt a b) 
  
  let rec print_env_item e =
    match e with
    | CST i         -> Printf.sprintf "Cst of %s" (string_of_int i)
    | CLS (c, d)    -> Printf.sprintf "Closure of (%s, %s)" "some code" "some env" 
    | CLSREC (c, d) -> Printf.sprintf "RecClosure of (some code, some env)"
    | BUILTCLS _    -> "BuiltinClosure"
    | REF r         -> "Ref value" 
    | ARR a         -> print_array a
    | UNIT          -> "UnitValue"
    | VOID          -> ""
    | ENV _         -> "Some Env"
    | CODE _        -> "Some code"
    | TUPLE l       -> Printf.sprintf "Tuple of length %s" (string_of_int (List.length l))
    | MARK          -> "Mark"
 
 (* affiche tout le contenu de l'environnement *)
  let print_env d =
    fold_left (fun a b -> a ^ " | " ^ b) "" (map  (fun i -> print_env_item i) (sub d.arr 0 (if d.start <= 0 then 1 else d.start)))

  let void = VOID 
  let size d = d.size

  (* fonction add, très importante :
   * elle ajoute un élément à l'environnement et augmente
   * l'indice de tous les autres *)
  let rec add d = function
    | UNIT -> ()
    | x ->
    if d.size = d.ssize then
      let a = make (2*d.ssize) void in
      begin
        let assign a i y = a.(i) <- y in
        iteri (assign a) d.arr;
        d.arr <- a;
        d.ssize <- 2 * (d.ssize);
        d.size <- d.size + 1;
        add d x
      end
    else
      begin
      d.size <- d.size + 1;
      d.start <- d.start + 1;
      d.arr.(d.start) <- x
      end
  
  let front d = d.arr.(d.start)

  let cut d = d.start <- d.start - 1

  let access d i =
    d.arr.(d.start-i)

  let init () =
    {ssize = 2 ; size = 0 ; arr = make 2 void ; start = -1}

  let first_index d x =
    let rec aux d x i =
      if (access d i) = x then i
      else aux d x (i+1)
    in aux d x 0
 
 (*
  let naming d x =
    if mem x d.arr then
      (first_index d x) + 1
    else
      failwith ("Error: Unbound value " ^ x)
  *)
  let copy d = { ssize = d.ssize ; size = d.size ; arr = Array.copy d.arr ; start = d.start }

end


(** MODULE Dream **)
(* Utilisé pour la conversion en indices de De Bruijn *)

module Dream =
struct 
  type dream = {mutable ssize:int; mutable size:int; mutable arr:string array; mutable start:int }

  let rec add d x =
    if d.size = d.ssize then
      let a = make (2*d.ssize) "" in
      begin
        let assign a i y = a.(i) <- y in
        iteri (assign a) d.arr;
        d.arr <- a;
        d.ssize <- 2 * (d.ssize);
        d.size <- d.size + 1;
        add d x
      end
    else
      begin
      d.size <- d.size + 1;
      d.start <- d.start + 1;
      d.arr.(d.start) <- x
      end

  let access d i =
    d.arr.(d.start-i)

  let init () =
    {ssize = 2; size = 0; arr = make 2 ""; start = -1}

  let first_index d x =
    let rec aux d x i =
      if (access d i) = x then i
      else aux d x (i+1)
    in aux d x 0

  let naming d x =
    if mem x d.arr then
      (first_index d x) + 1
    else
      failwith (Printf.sprintf "Error: Unbound value %s" x)

  let size d = d.size
  let get_mem d = d.arr

  let copy d = { ssize = d.ssize; size = d.size; arr = Array.copy d.arr; start = d.start }

end
