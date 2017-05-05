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

  type ('a) t = {mem: 'a E.t; types: Expr.type_listing E.t; user_defined_types: (identifier * int * (type_listing * type_declaration)) list}

  let create = {mem = E.empty; types = E.empty; user_defined_types = []}

  let disp_type map =
    E.iter (fun x y -> print_string @@ x ^ " ") map.types;
    print_string "\n"
  let disp map =
    E.iter (fun x y -> print_string @@ x ^ " ") map.mem;
    print_string "\n"

  let _find_latest_userdef map key =
    List.fold_left (fun i (n, b, _) -> if n = key && b > i then b else i) 0 map.user_defined_types

  let add_userdef map key parameters what =
    let next = _find_latest_userdef map key  + 1
    in {map with user_defined_types = (key, next, (parameters, what))::map.user_defined_types}



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
  | FConstructor of Expr.identifier * fouine_values 
  | FConstructor_noarg of Expr.identifier









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
  | FConstructor_noarg name, FConstructor_noarg name' -> name = name'
  | FConstructor (name, t), FConstructor(name', t') -> name = name' && ast_equal t t'
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
  | FConstructor_noarg name, FConstructor_noarg name' -> name < name'
  | FConstructor (name, t), FConstructor(name', t') -> name < name' && ast_equal t t'
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
