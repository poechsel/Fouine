(* the environment. It is made of Maps, 
   because they already implements stacking,
   which just make our life easier. Unfortunately,
   we are loosing a bit in performance. But due to 
   the short deadline, it is a good compromise.
   
   This environment is in fact made of two environments:
   one for types, the other for evaluation *)


open Errors
open Binop
open Expr

module Env =
struct 
  module E = Map.Make(struct
      type t = string
      let compare = Pervasives.compare
    end)

  type ('a) t = {mem: 'a E.t; types: Expr.type_listing E.t; user_defined_types: (identifier * int * (type_listing list * type_listing)) list}

  let create = {mem = E.empty; types = E.empty; user_defined_types = []}

  let disp_type map =
    E.iter (fun x y -> print_string @@ x ^ " ") map.types;
    print_string "\n"
  let disp map =
    E.iter (fun x y -> print_string @@ x ^ " ") map.mem;
    print_string "\n"

  let _find_latest_userdef map key params_size =
    List.fold_left (fun i (n, b, (p, _)) -> if n = key && List.length p = params_size && b > i then b else i) (-1) map.user_defined_types
  
  let rec _update_types_pointer map t = 
    let aux = _update_types_pointer map in
    match t with
    | Called_type (name, x, a) when x < 0 -> 
      let id = _find_latest_userdef map name (List.length a)
      in let _ = Printf.printf "updated with id %d\n" id
      in if id = -1 then failwith "undefined type"
      else Called_type (name, id, a) 
    | Tuple_type l -> Tuple_type (List.map aux l)
    | Array_type l -> Array_type (aux l)
    | Ref_type l -> Ref_type (aux l)
    | Fun_type (a, b) -> Fun_type (aux a, aux b)
    | Var_type ({contents = Link x} as y) -> y := Link(aux x); t
    | _ -> t

  let get_corresponding_id map what =
    match what with
    | Called_type (name, id, params) ->
      let current_id = if id < 0 then 
          _find_latest_userdef map name (List.length params)
        else id
      in Called_type (name, current_id, params)
    | _ -> failwith "called type awaited"

  let get_latest_userdef map name id params =
      let current_id = if id < 0 then 
          _find_latest_userdef map name (List.length params)
        else id
      in let (_, _, (params_t, t)) = List.find (fun (n, i, _) -> n = name && i = current_id) map.user_defined_types
      in (Called_type(name, current_id, params_t), t)



  let add_userdef map new_type =
    match new_type with
    | TypeDecl(Called_type(key, _, parameters), what, _) ->
      let next_id = _find_latest_userdef map key (List.length parameters) + 1
      in let _  = Printf.printf "new user type at id %d\n" next_id
      in begin match what with
      | Basic_type t ->
        { map with user_defined_types = (key, next_id, (parameters, _update_types_pointer map t)) :: map.user_defined_types}
      | Constructor_list l ->
        let next_type = Called_type(key, next_id, parameters) in
        let map = { map with user_defined_types = (key, next_id, (parameters, next_type)) :: map.user_defined_types}
        in List.fold_left (
          fun a b ->
            match b with
            | Constructor_type (name, _, args) ->
              let args = match args with
                | None -> None
                | Some x -> Some (_update_types_pointer a x)
              in let next_id_constr = _find_latest_userdef a name 0
              in { a with user_defined_types = (name, next_id_constr, (parameters, Constructor_type(name, next_type, args))) :: a.user_defined_types}
            | _ -> failwith "waited for a constructor"
        ) map l
          end
      | _ -> failwith "waited for a type declaration"



  let mem map key =
    E.mem (string_of_ident key) map.mem
  let remove map key = 
    E.remove (string_of_ident key) map.mem
  let add map key prog =
    { map with mem = E.add (string_of_ident key) prog map.mem }
  let get_most_recent map key = 
    E.find (string_of_ident key) map.mem
  let add_type map key t =
    {map with types = E.add (string_of_ident key) t map.types}
  let mem_type map key = 
    E.mem (string_of_ident key) map.types
  let get_type map key = 
    E.find (string_of_ident key) map.types
end

type fouine_values =
  | FTuple  of fouine_values list
  | FInt    of int
  | FBool   of bool
  | FUnit   
  | FArray  of int array
  | FRef    of fouine_values ref
  | FClosure of fouine_values Expr.expr * fouine_values Expr.expr * fouine_values Env.t
  | FClosureRec of identifier * fouine_values Expr.expr * fouine_values Expr.expr * fouine_values Env.t
  | FBuildin  of (fouine_values -> fouine_values)
  | FConstructor of Expr.identifier * fouine_values perhaps









let action_wrapper_arithms action a b error_infos s = 
  match (a, b) with
  | FInt x, FInt y -> (FInt ( action x y ))
  | _ -> raise (send_error ("This arithmetic operation (" ^ s ^ ") only works on integers") error_infos)

let type_checker_arithms = Fun_type(Int_type, Fun_type(Int_type, Int_type))


(* interpretation function and type of an operation dealing with ineqalities *)
let action_wrapper_ineq (action : 'a -> 'a -> bool) a b error_infos s =
  match (a, b) with
  | FInt x, FInt y -> FBool (action x y)
  | FBool x, FBool y -> FBool (action (int_of_bool x) (int_of_bool y))
  | _ -> raise (send_error ("This comparison operation (" ^ s ^ ") only works on objects of the same type") error_infos)

let type_checker_ineq  =
  let new_type = Generic_type (new_generic_id ())
  in
  Fun_type(new_type, Fun_type(new_type, Bool_type))

let rec ast_equal a b = 
  match a, b with
  | FBool x, FBool y -> x = y
  | FInt x, FInt y -> x = y
  | FArray x, FArray y -> x = y
  | FTuple l , FTuple l' when List.length l = List.length l' -> List.for_all2 ast_equal l l'
  | FConstructor (name, None), FConstructor (name', None) -> name = name'
  | FConstructor (name, Some t), FConstructor(name', Some t') -> name = name' && ast_equal t t'
  | _ -> false
let rec ast_slt a b = 
  match a, b with
  | FBool x, FBool y -> x < y
  | FInt x, FInt y -> x < y
  | FArray x, FArray y -> x < y
  | FTuple l, FTuple l' when List.length l = List.length l' -> 
    let rec aux l l' = 
      match (l, l') with
      | x::tl, y::tl' when x = y -> aux tl tl'
      | x::tl, y::tl' when x < y -> true
      | _ -> false
    in aux l l'
  | FConstructor (name, None), FConstructor (name', None) -> name < name'
  | FConstructor (name, Some t), FConstructor(name', Some t') -> name < name' && ast_equal t t'
  | _ -> false
let ast_slt_or_equal a b  = ast_equal a b || ast_slt a b
let ast_nequal a b = not (ast_equal a b)
let ast_glt a b = not (ast_slt_or_equal a b) 
let ast_glt_or_equal a b = not (ast_slt a b) 


(* interpretation function and type of a boolean operation *)
let action_wrapper_boolop action a b error_infos s =
  match (a, b) with
  | FBool x, FBool y -> FBool (action x y)
  | _ -> raise (send_error ("This boolean operation (" ^ s ^ ") only works on booleans") error_infos)
let type_checker_boolop  =
  Fun_type(Bool_type, Fun_type(Bool_type, Bool_type))

(* interpretation function and type of a reflet *)
let action_reflet a b error_infos s =
  match (a) with 
  | FRef(x) -> x := b; FUnit
  | _ -> raise (send_error "Can't set a non ref value" error_infos)

let type_checker_reflet  = 
  let new_type = Generic_type (new_generic_id ())
  in Fun_type(Ref_type(new_type), Fun_type(new_type, Unit_type))


(* all of our binary operators *)
let addOp = new binOp "+"  3 (action_wrapper_arithms (+)) type_checker_arithms
let minusOp = new binOp "-" 3  (action_wrapper_arithms (-)) type_checker_arithms
let multOp = new binOp "*" 4 (action_wrapper_arithms ( * )) type_checker_arithms
let divOp = new binOp "/" 4 (action_wrapper_arithms (/)) type_checker_arithms
let eqOp = new binOp "=" 2 (fun a b c d -> FBool(ast_equal a b)) type_checker_ineq
let neqOp = new binOp "<>" 2 (fun a b c d -> FBool(ast_nequal a b)) type_checker_ineq
let gtOp = new binOp ">=" 2 (fun a b c d -> FBool(ast_glt_or_equal a b)) type_checker_ineq
let sgtOp = new binOp ">" 2 (fun a b c d -> FBool(ast_glt a b)) type_checker_ineq
let ltOp = new binOp "<=" 2 (fun a b c d -> FBool(ast_slt_or_equal a b)) type_checker_ineq
let sltOp = new binOp "<" 2 (fun a b c d -> FBool(ast_slt a b)) type_checker_ineq
let andOp = new binOp "&&" 2 (action_wrapper_boolop (&&)) type_checker_boolop
let orOp = new binOp "||" 2 (action_wrapper_boolop (||)) type_checker_boolop

let refSet = new binOp ":=" 0 action_reflet type_checker_reflet
