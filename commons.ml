
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


let rec list_of_array ar =
  let rec aux i =
    if i = Array.length ar then
      []
    else
      ar.(i) :: aux (i+1)
  in aux 0

(* check if a list is made of unique elements *)
let list_has_unique_elements l =
  let rec aux l l' = List.length l = List.length l'
  in aux (List.sort_uniq compare l) l
