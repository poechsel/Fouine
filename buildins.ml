let list_none = "Buildins_None_List"
let list_elt = "Buildins_Elt_List"

let list_type_declaration =
  Printf.sprintf "type 'a list = %s | %s of ('a * 'a list);;" list_none list_elt
