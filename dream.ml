(* lib for dream environment for all compilation machine and Bruijn pre-process *)
open Array
open Expr
open Binop
open Isa
open Env

(* builtin functions --> l.48 *)


(* to do : faire des fonctions pour accéder aux champs de l'énumération dream
 * et créer un foncteur qui génère tous mes environnements *)

(* to do : donner un module en argument pour ne pas avoir à utiliser Isa.ml et 
 * supprimer la dépendance circulaire *)

(*module DreamMaker ( : DreamPattern) = struct
   
end*)

let mem a l =
  let rec aux i =
    if i = Array.length l then
      false
    else 
    if l.(i) = a then true
    else aux (i+1)
  in aux 0

module DreamEnv =
struct

(*  type builtin_type =*)
  type builtin_type = instr -> instr
  type item =
    | CST of int
    | CLS of code * dream
    | CLSREC of code * dream
    | BUILTCLS of (item -> item) 
    | REF of item ref
    | ARR of int array
    | VOID
    | CODE of code
    | ENV of dream
  and dream = {mutable ssize:int ; mutable size:int ; mutable arr:(item array) ; builtin:((item->item, item) Env.t) ; mutable start:int }

  (* lib contenant les fonctions builtin 
     il suffit d'ajouter le nom de la fonction, et la fonction
     qui est de type item -> item *)

  let lib = [("print",
              fun x ->
                begin
                  match x with
                  | CST k -> print_endline (string_of_int k); CST k
                  | _ -> failwith "Error: prInt type"
                end
              )]

  let is_builtin x =
    let rec aux x = function
      | [] -> false
      | (key, _) :: q -> if key = x then true else (aux x q)        
    in aux x lib

  let rec load_lib e = function
    | [] -> e
    | (key, func) :: xs -> Env.add (load_lib e xs) key func 

  let get_builtin d f = Env.get_most_recent (d.builtin) f 

  let rec print_env_item e =
    match e with
    | CST i -> Printf.sprintf "CST of %s" (string_of_int i)
    | CLS (c, d) -> Printf.sprintf "CLS of (%s, %s)" "some code" "some env" 
    | CLSREC (c, d) -> Printf.sprintf "CLSREC of (some code, some env)"
    | REF r -> "REF value" 
    | ARR a -> "an array"
    | VOID -> ""
    | _ -> "please implement"
  
  and print_env d =
    fold_left (fun a b -> a ^ " | " ^ b) "" (map  (fun i -> print_env_item i) d.arr) 

  let void = VOID 
  let size d = d.size

  let rec add d x =
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
    let e = load_lib (Env.create) lib in
    {ssize = 2 ; size = 0 ; arr = make 2 void ; builtin = e ; start = -1}

  let first_index d x =
    let rec aux d x i =
      if (access d i) = x then i
      else aux d x (i+1)
    in aux d x 0

  let naming d x =
    if mem x d.arr then
      (first_index d x) + 1
    else
      failwith "Error: Unbound value y" (*
      begin
      add d x;
      1
      end *)

  let copy d = { ssize = d.ssize ; size = d.size ; arr = Array.copy d.arr ; builtin = d.builtin ; start = d.start }

  end

module Dream =
struct 
  type dream = {mutable ssize:int; mutable size:int; mutable arr:string array; mutable start:int }
  (* structural size
  *  physical size
  *  array 
  *  top of stack *)

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
      failwith (Printf.sprintf "Error: Unbound value %s" x) (*
      begin
      add d x;
      1
      end *)

  let size d = d.size
  let get_mem d = d.arr

  let copy d = { ssize = d.ssize; size = d.size; arr = Array.copy d.arr; start = d.start }
  end

(* third env for krivine machine *)

module DreamKriv = struct
  type env_item = Thunk of code * dream | Void
  and dream = {mutable ssize:int; mutable size:int; mutable arr:env_item array; mutable start:int }

  let void = Void

  let rec add d x =
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
    {ssize = 2; size = 0; arr = make 2 void; start = -1}

  let first_index d x =
    let rec aux d x i =
      if (access d i) = x then i
      else aux d x (i+1)
    in aux d x 0

  let naming d x =
    if mem x d.arr then
      (first_index d x) + 1
    else
      begin
      add d x;
      1
      end

  let copy d = { ssize = d.ssize; size = d.size; arr = Array.copy d.arr; start = d.start }

end

