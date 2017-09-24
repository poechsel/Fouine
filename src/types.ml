open Commons

(* structure for types *)
type types =
  | Int
  | Bool
  | Unit
  | Array       of types
  | Var         of tv ref
  | Ref         of types
  | Fun         of types * types
  | Tuple       of types list
    (* a constructor has a name, a father, and a type *)
  | Constructor of identifier * types * types perhaps 
  | Generic     of int
    (*for a polymoric type *)
  | Polymorphic of string     
    (* for types like ('a, 'b) expr *)
  | Called      of identifier * int * types list 

and tv = Unbound of int * int | Link of types



type user_defined =
  | Renamed_decl     of types
  | Sum_decl         of types
  | Constructor_decl of types
  | Module_sig_decl  of module_type_listing list
and declaration =
  | Constructor_list of types list
  | Basic            of types
  | Module           of module_type_listing list


and module_type_listing =
  | Val_entry  of identifier * types
  | Type_entry of types * types perhaps

type module_signature = 
  | Register   of identifier
  | Unregister of module_type_listing list



type sum =
  | CType_cst of string
  | CType     of string * types


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
    Printf.sprintf "%c" c 

let pretty_print_aux t tbl = 
  let rec add_parenthesis a = 
    if is_atomic a then aux a
    else "("^aux a^")"
  and aux t=
    match t with
    | Int -> 
      "int"
    | Bool -> 
      "bool"
    | Array x -> 
      aux x ^ " array"
    | Ref x -> 
      Printf.sprintf "ref %s" (aux x)
    | Unit -> 
      "unit"
    | Var x -> 
      begin
        match (!x) with
        | Unbound (y, _) ->                      (* a bit long, because we are trying to mimic the formating of caml *)
          "'_"^print_polymorphic tbl y
        | Link l -> aux l
      end
    | Generic y ->
      "'" ^ print_polymorphic tbl y
    | Fun (a, b) ->  
      Printf.sprintf ("%s -> %s") (add_parenthesis a) (aux b)
    | Tuple l -> 
      List.fold_left 
        (fun a b ->  a ^ " * " ^ (add_parenthesis b)) 
        (add_parenthesis @@ List.hd l) 
        (List.tl l)
    | Constructor (name, father, Some t) ->
      Printf.sprintf "%s of (%s)" 
        (string_of_ident name)  
        (add_parenthesis t) 
    | Constructor(name, father, None) ->
      (string_of_ident name)
    | Polymorphic l -> "["^l^"]"
    | Called (name, i, params) ->
      if params = [] then
        string_of_ident name ^ " : " ^ string_of_int i
      else 
        let temp =
          List.fold_left 
            (fun a b -> a ^ ", " ^ (add_parenthesis b)) 
            (add_parenthesis @@ List.hd params) 
            (List.tl params)
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



