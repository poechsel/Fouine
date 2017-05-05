(* the environment. It is made of Maps, 
   because they already implements stacking,
   which just make our life easier. Unfortunately,
   we are loosing a bit in performance. But due to 
   the short deadline, it is a good compromise.
   
   This environment is in fact made of two environments:
   one for types, the other for evaluation *)




module Env =
struct 
  module E = Map.Make(struct
      type t = string
      let compare = Pervasives.compare
    end)

  type ('a, 'b, 'c) r = {env : (('a, 'b, 'c) t) ref; params: 'b; def : 'c}
  and ('a, 'b, 'c) t = {mem: 'a E.t; types: 'b E.t; user_defined_types: (('a, 'b, 'c) r) E.t}

  let create = {mem = E.empty; types = E.empty; user_defined_types = E.empty}

  let disp_type map =
    E.iter (fun x y -> print_string @@ x ^ " ") map.types;
    print_string "\n"
  let disp map =
    E.iter (fun x y -> print_string @@ x ^ " ") map.mem;
    print_string "\n"
  let mem map key =
    E.mem key map.mem
  let remove map key = 
    E.remove key map.mem
  let add map key prog =
    { map with mem = E.add key prog map.mem }
  let get_most_recent map key = 
    E.find key map.mem
  let add_type map key t =
    {map with types = E.add key t map.types}
  let mem_type map key = 
    E.mem key map.types
  let get_type map key = 
    E.find key map.types
end
;;

