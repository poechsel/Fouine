(* lib for dream environment for zinc machine and eventually secd *)
open Array

module Dream =
struct
type dream = {mutable ssize:int; mutable size:int; mutable arr:string array; mutable start:int }
(* structural size
*  physical size
*  array *)

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
    begin
    add d x;
    1
    end

let copy d = { ssize = d.ssize; size = d.size; arr = Array.copy d.arr; start = d.start }
end
