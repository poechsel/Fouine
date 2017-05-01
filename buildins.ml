let list_none = "Buildins_None_List"
let list_elt = "Buildins_Elt_List"

let list_type_declaration =
  Printf.sprintf "type 'a list = %s | %s of ('a * 'a list);;" list_none list_elt

let list_concat =
  "let rec (@) l1 l2 = match l1 with
    | [] -> l2
    | x::tl -> x::(tl @ l2);;"

let buildins_create = "let buildins_create = (0, Buildins_None_List);;"
let create_repl_ref = "let tr_memory = buildins_create;;" 

