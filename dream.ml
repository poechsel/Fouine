(* lib for dream environment for all compilation machine and Bruijn pre-process *)
open Array
open Expr
open Binop
open Isa

(* to do : faire des fonctions pour accéder aux champs de l'énumération dream
 * et créer un foncteur qui génère tous mes environnements *)

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
  type env_items =
    | EnvCST of int
    | EnvCLS of code * dream
    | EnvCLSREC of code * dream
    | EnvREF of int ref
    | EnvARR of int array
    | VOID
  and dream = {mutable ssize:int; mutable size:int; mutable arr:env_items array; mutable start:int }


  let rec print_env_item e =
    match e with
    | EnvCST i -> Printf.sprintf "EnvCST of %s" (string_of_int i)
    | EnvCLS (c, d) -> Printf.sprintf "EnvCLS of (%s, %s)" "some code" "some env" 
    | EnvCLSREC (c, d) -> Printf.sprintf "EnvCLSREC of (some code, some env)"
    | EnvREF r -> Printf.sprintf "EnvREF of %s" (string_of_int !r)
    | EnvARR a -> "an array"
    | VOID -> Printf.sprintf ""
  and print_env d =
    fold_left (fun a b -> a ^ " | " ^ b) "" (map  (fun i -> print_env_item i) d.arr) 
  (* structural size
  *  physical size
  *  arrasy 
  *  top of stack *)

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
      failwith "Error: Unbound value y" (*
      begin
      add d x;
      1
      end *)

  let copy d = { ssize = d.ssize; size = d.size; arr = Array.copy d.arr; start = d.start }

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

  let copy d = { ssize = d.ssize; size = d.size; arr = Array.copy d.arr; start = d.start }
  end


(* third env for krivine machine *)

module DreamKriv = struct
  type env_items = Thunk of code * dream | Void
  and dream = {mutable ssize:int; mutable size:int; mutable arr:env_items array; mutable start:int }

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

