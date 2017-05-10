open Expr


let list_none = ([], "Buildins_None_List")
let list_elt = ([], "Buildins_Elt_List")

(* declaration of a list *)
let list_type_declaration =
  Printf.sprintf "type 'a list = %s | %s of ('a * 'a list);;" "Buildins_None_List" "Buildins_Elt_List"

(* list concatenation *)
let list_concat =
  "let rec (@) l1 l2 = match l1 with
    | [] -> l2
    | x::tl -> x::(tl @ l2);;"


(* buildins for ref transformation *)
let buildins_create = "let buildins_create = (0, Buildins_None_List);;"
let create_repl_ref = "let tr_memory = buildins_create;;" 
let buildins_ref = ["
let buildins_allocate v env =
  let (x, env) = env
  in (x, (x+1, Buildins_Elt_List ((x, v), env)));;
";"
let buildins_read v env =
  let (x, env) = env in
  let rec aux l =
    match l with
    | Buildins_None_List -> raise (E 0)
    | Buildins_Elt_List ((r, w), tl) ->
      if r = v then 
        w
        else 
          aux tl
  in (aux env);;
";
"
let buildins_modify env (re, value)=
  let (x, env) = env in
  let rec aux l =
    match l with
    | Buildins_None_List -> l
    | Buildins_Elt_List ((r, w), tl) ->
      if r=re  then 
        Buildins_Elt_List((r, value), aux tl)
      else 
        Buildins_Elt_List((r, w), aux tl)
  in (x, aux env);;
"]

(* buildin for fix point *)
let buildins_fix = ["
type 'a fix = Buildins_Fix of ('a fix -> 'a);;";"
let buildins_y t = let p (Buildins_Fix f) x = t (f (Buildins_Fix f)) x in p (Buildins_Fix p);;
  "]
