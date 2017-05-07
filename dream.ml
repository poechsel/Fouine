(* lib for dream environment for all compilation machine and Bruijn pre-process *)
open Array
open Binop
open Env

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

(* MODULE DreamEnv *)
(* Utilisé par la SECD *)

module DreamEnv =
struct

(*  type builtin_type =*)
  type 'a item =
    | CST of int
    | CLS of 'a * 'a dream
    | CLSREC of 'a * 'a dream
    | BUILTCLS of ('a item -> 'a item) 
    | REF of 'a item ref
    | ARR of int array
    | VOID
    | CODE of 'a
    | ENV of 'a dream
    | UNIT
    | MARK
    | TUPLE of ('a item list)
  (* dream est le type de l'environnement *)
  and 'a dream = {mutable ssize:int ; mutable size:int ; mutable arr:('a item array) ; builtin:(('a item->'a item, 'a item) Env.t) ; mutable start:int }

  (* Feature : on peut réserver des identifiants à des fonctions 
   * prédéfinies. Pour cela, il suffit d'ajouter des éléments à
   * la liste lib. 
   *
   * Désactivé pour le moment *)

  (* lib contenant les fonctions builtin 
     il suffit d'ajouter le nom de la fonction, et la fonction
     qui est de type item -> item *)

  (*
  let lib = [("prInt",
              fun x ->
                begin
                  match x with
                  | CST k -> print_endline (string_of_int k); CST k
                  | _ -> failwith "Error: prInt type"
                end
              )] *)

  let lib = []

  let is_builtin x =
    let rec aux x = function
      | [] -> false
      | (key, _) :: q -> if key = x then true else (aux x q)        
    in aux x lib

  let rec load_lib e = function
    | [] -> e
    | (key, func) :: xs -> Env.add (load_lib e xs) key func 

  let get_builtin d f = Env.get_most_recent (d.builtin) f 

  (* afficher un item *)
  let rec print_env_item e =
    match e with
    | CST i -> Printf.sprintf "CST of %s" (string_of_int i)
    | CLS (c, d) -> Printf.sprintf "CLS of (%s, %s)" "some code" "some env" 
    | CLSREC (c, d) -> Printf.sprintf "CLSREC of (some code, some env)"
    | BUILTCLS _ -> "BUILTCLS"
    | REF r -> "REF value" 
    | ARR a -> "an array"
    | UNIT -> "UNIT"
    | VOID -> ""
    | ENV _ -> "ENV"
    | CODE _ -> "CODE"
    | TUPLE l -> Printf.sprintf "TUPLE of length %s" (string_of_int (List.length l))
    | MARK -> "MARK"
 
 (* affiche tout le contenu de l'environnement *)
  and print_env d =
    fold_left (fun a b -> a ^ " | " ^ b) "" (map  (fun i -> print_env_item i) d.arr) 

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


(** MODULE Dream **)
(* Utilisé pour la conversion en indices de De Bruijn *)

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

