(* the environment. It is made of Maps, 
   because they already implements stacking,
   which just make our life easier. Unfortunately,
   we are loosing a bit in performance. But due to 
   the short deadline, it is a good compromise.
   
   This environment is in fact made of two environments:
   one for types, the other for evaluation *)

open Commons
open Errors
open Binop
open Expr

let buildins_activated = ref true

module SubEnv =
struct 
  module E = Map.Make(struct
      type t = string
      let compare = Pervasives.compare
    end)


(* a simple env is composed of three things:
   - a memory, mem, containing different functions bindings
   - an environment containing current type bindings
   - a list containing all user defined types. We use a list here to show that we can simulate "closure" 
   without saving the environment in a closure *)
  type 'a t = {mem: 'a E.t; 
                 types: Types.types E.t; 
                 user_defined_types: (identifier * int * (Types.types list * Types.user_defined)) list}

  let create = {mem = E.empty; 
                types = E.empty; 
                user_defined_types = []}

  let disp_type map =
    E.iter (fun x y -> print_string @@ x ^ " ") map.types;
    print_string "\n"
  let disp map =
    E.iter (fun x y -> print_string @@ x ^ " ") map.mem;
    print_string "\n"

    let disp_bloc env ident = 
      print_endline @@ ident ^ "vars: ";
        E.iter (fun x _ -> print_endline @@ (ident ^ "  ") ^ x) env.mem


    (* find the last userdefine types having a certain name and a certain number of parameters *)
  let _find_latest_userdef map key params_size =
    List.fold_left 
      (fun i (n, b, (p, _)) -> 
         if n = key && List.length p = params_size && b > i then 
           b 
         else i
      ) (-1) map.user_defined_types
  
(* update a type so that each user defined sub types targets the last types with this name
   declared*)
  let rec _update_types_pointer map t = 
    let aux = _update_types_pointer map in
    match t with
    | Types.Called (name, x, a) when x < 0 -> 
      let id = _find_latest_userdef map name (List.length a)
      in let _ = Printf.printf "updated with id %d\n" id
      in if id = -1 then 
        raise (send_inference_error Lexing.dummy_pos "can't update type" )
        failwith "undefined type"
      else Types.Called (name, id, a) 
    | Types.Tuple l -> 
      Types.Tuple (List.map aux l)
    | Types.Array l -> 
      Types.Array (aux l)
    | Types.Ref l -> 
      Types.Ref (aux l)
    | Types.Fun (a, b) -> 
      Types.Fun (aux a, aux b)
    | Types.Var ({contents = Types.Link x} as y) -> 
      y := Types.Link(aux x); t
    | _ -> t


  (* update the name of a type so that it points to the most recent type of this name *)
  let get_corresponding_id map what =
    match what with
    | Types.Called (name, id, params) ->
      let current_id = if id < 0 then 
          _find_latest_userdef map name (List.length params)
        else id
      in Types.Called (name, current_id, params)
    | _ -> failwith "called type awaited"


  (* get the latest user defined type having a certain name and a certain number of parameters*)
  let get_latest_userdef map name id params =
      let current_id = if id < 0 then 
          _find_latest_userdef map name (List.length params)
        else id
      in let (_, _, (params_t, t)) = 
           List.find (fun (n, i, _) -> n = name && i = current_id) map.user_defined_types
      in (Types.Called(name, current_id, params_t), t)



  (* add a userdefined type *)
  let add_userdef map new_type =
    match new_type with
    | TypeDecl(Types.Called(key, _, parameters), what, _) ->
      let next_id = _find_latest_userdef map key (List.length parameters) + 1
      in begin match what with
      | Types.Module l ->
        let key = (fst key, "_" ^ snd key) in
        { map with user_defined_types = (key, next_id, (parameters, Module_sig_decl l)) :: map.user_defined_types}
      | Types.Basic t ->
        { map with user_defined_types = (key, next_id, (parameters, Renamed_decl (_update_types_pointer map t))) :: map.user_defined_types}
      | Types.Constructor_list l ->
        let next_type = Types.Called(key, next_id, parameters) in
        let map = { map with user_defined_types = (key, next_id, (parameters, Sum_decl next_type)) :: map.user_defined_types}
        in List.fold_left (
          fun a b ->
            match b with
            | Types.Constructor (name, _, args) ->
              let args = match args with
                | None -> None
                | Some x -> Some (_update_types_pointer a x)
              in let next_id_constr = _find_latest_userdef a name 0
              in { a with user_defined_types = (name, next_id_constr, (parameters, Constructor_decl(Types.Constructor(name, next_type, args)))) :: a.user_defined_types}
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
    (* get the most recent binding *)
  let get_most_recent map key = 
    E.find (string_of_ident key) map.mem
  let add_type map key t =
    {map with types = E.add (string_of_ident key) t map.types}
  let mem_type map key = 
    E.mem (string_of_ident key) map.types
  let get_type map key = 
    E.find (string_of_ident key) map.types
end

let rec show_all_fouine_files () =
  File.seek_module "Ref"



module Env =
struct 
  module E = Map.Make(struct
      type t = string
      let compare = Pervasives.compare
    end)

  type 'a sub_element = Node of ('a sub_element) E.t * 'a SubEnv.t

  (* an environment is a tree of subenv. Each subenv corresponds to a new module *)
  type 'a t = string list * 'a sub_element




  let create = let temp = E.empty
    in ([], (Node (E.empty, SubEnv.create)))

  let disp env =
    let _ = print_endline "======== ENV =======" in
    let rec aux env ident =
      match env with
      | Node(sub, e) ->
        let _ = SubEnv.disp_bloc e ident
        in E.iter (fun a b ->
            let _ = print_endline @@ ident ^ "-> " ^a 
            in aux b (ident ^ "  "))
          sub
    in let _ = aux (snd env) ""
  in print_endline "======== === ======="




     (* apply a function fct on the subenv corresponding to the module
        path_key. This fonction must return nothing

        If the module isn't here, we try to load it lazily by looking in the files.
        It will be loaded only one time, because we add it to the environment later one *)
  let rec get_corresponding_subenv env (path_key, id) fct =
    let path, subenv_lists = env
    in let rec aux path subenv = 
         match (path, subenv) with
        | [], Node (sub, env) -> 
          fct env ([], id)
        | x :: t, Node(sub, env) -> 
          if E.mem x sub then 
            aux t (E.find x sub)
          else 
            raise Not_found
(* this iteration is here for nothing. Normally it was here for when 
   we will add an open command, but it never happened *)
    in let rec test_paths path = 
         match path with
         | [] -> 
           aux (List.rev path_key) subenv_lists
         | x::tl ->        
           begin try
               aux (List.rev (path_key @ path)) subenv_lists
             with _ ->
               test_paths tl
           end
    in begin try 
        test_paths path
      with Not_found ->
        (* lazzy loading *)
        if List.length path_key = 0 then raise Not_found
        else 
          let _, Node(subenv, _) = env
          in if E.mem (List.hd path_key) subenv then raise Not_found
          else
        let path = File.seek_module (List.hd path_key)
        in raise (LoadModule (List.hd path_key, path))
    end



(* add something to an environment. This is done thanks to the function 
   fct which does the job when we have the subenv *)
  let rec add_corresponding_subenv env fct  =
    let path_current, subenv_lists = env
    in let rec aux path subenv = 
          match (path, subenv) with
            | [], Node (sub, env) ->  
              Node(sub, fct env)
        | x :: t, Node(sub, env) -> 
          if E.mem x sub then 
            Node(E.add x (aux t (E.find x sub)) sub, env)
        else 
          raise Not_found 
    in path_current, aux (List.rev path_current) subenv_lists

  let enter_module env name =
    let p, e = env in
    name :: p, e
  let quit_module env name =
    let _::p, e = env in
    p, e

  (* create a module *)
  let create_module env name =
    let path_current, subenv_lists = env
    in let rec aux path subenv = match (path, subenv) with
        | [], Node (sub, env) -> 
          Node(E.add name (Node(E.empty, SubEnv.create)) sub, env)
        | x :: t, Node(sub, env) -> 
          if E.mem x sub then 
            Node(E.add x (aux t (E.find x sub)) sub, env) 
          else 
            raise Not_found 
    in path_current, aux (List.rev path_current) subenv_lists



  (* just some adaptations *)
  let get_corresponding_id map what =
    let Types.Called(name, i, l) = what in 
    get_corresponding_subenv map name 
      (fun env name -> SubEnv.get_corresponding_id env (Types.Called(name, i, l)))

  let get_latest_userdef map name id params =
    get_corresponding_subenv map name 
      (fun env name -> SubEnv.get_latest_userdef env name id params)

  let add_userdef map new_type =
    add_corresponding_subenv map (fun a -> SubEnv.add_userdef a new_type)

  let mem map key =
    get_corresponding_subenv map key (fun env name -> SubEnv.mem env name)
  let add map key prog =
    add_corresponding_subenv map (fun a -> SubEnv.add a key prog)
  let get_most_recent map key = 
    get_corresponding_subenv map key (fun env name -> SubEnv.get_most_recent env name)
  let add_type map key t =
    add_corresponding_subenv map (fun a -> SubEnv.add_type a key t)
  let mem_type map key = 
    get_corresponding_subenv map key (fun env name -> SubEnv.mem_type env name)
  let get_type map key = 
    get_corresponding_subenv map key (fun env name -> SubEnv.get_type env name)

end


type fouine_values =
  | FUnit
  | FTuple       of fouine_values list
  | FInt         of int
  | FBool        of bool
  | FArray       of int array
  | FRef         of fouine_values ref
  | FClosure     of fouine_values Expr.expr * fouine_values Expr.expr * fouine_values Env.t
  | FClosureRec  of identifier * fouine_values Expr.expr * fouine_values Expr.expr * fouine_values Env.t
  | FBuildin     of (fouine_values -> fouine_values)
  | FConstructor of identifier * fouine_values perhaps





let action_wrapper_arithms action a b error_infos s = 
  match (a, b) with
  | FInt x, FInt y -> 
    FInt ( action x y )
  | _ -> 
    raise (send_error 
             ("This arithmetic operation (" ^ s ^ ") only works on integers") 
             error_infos)

let type_checker_arithms = Types.Fun(Types.Int, Types.Fun(Types.Int, Types.Int))


(* interpretation function and type of an operation dealing with ineqalities *)
let action_wrapper_ineq (action : 'a -> 'a -> bool) a b error_infos s =
  match (a, b) with
  | FInt x, FInt y -> 
    FBool (action x y)
  | FBool x, FBool y -> 
    FBool (action (int_of_bool x) (int_of_bool y))
  | _ -> raise (send_error 
                  ("This comparison operation (" ^ s ^ ") only works on objects of the same type") 
                  error_infos)


let type_checker_ineq  =
  let new_type = Types.Generic (Types.new_generic_id ())
  in Types.Fun(new_type, Types.Fun(new_type, Types.Bool))

let rec ast_equal a b = 
  match a, b with
  | FBool x, FBool y -> 
    x = y
  | FInt x, FInt y -> 
    x = y
  | FArray x, FArray y -> 
    x = y
  | FTuple l , FTuple l' when List.length l = List.length l' -> 
    List.for_all2 ast_equal l l'
  | FConstructor (name, None), FConstructor (name', None) -> 
    name = name'
  | FConstructor (name, Some t), FConstructor(name', Some t') -> 
    name = name' && ast_equal t t'
  | _ -> false


let rec ast_slt a b = 
  match a, b with
  | FBool x, FBool y ->
    x < y
  | FInt x, FInt y -> 
    x < y
  | FArray x, FArray y -> 
    x < y
  | FTuple l, FTuple l' when List.length l = List.length l' -> 
    let rec aux l l' = 
      match (l, l') with
      | x::tl, y::tl' when ast_equal x y -> aux tl tl'
      | x::tl, y::tl' when ast_slt x y -> true
      | _ -> false
    in aux l l'
  | FConstructor (name, None), FConstructor (name', None) -> 
    name < name'
  | FConstructor (name, Some t), FConstructor(name', Some t') -> 
    name < name' && ast_equal t t'
  | _ -> false

let ast_slt_or_equal a b  = ast_equal a b || ast_slt a b
let ast_nequal a b = not (ast_equal a b)
let ast_glt a b = not (ast_slt_or_equal a b) 
let ast_glt_or_equal a b = not (ast_slt a b) 


(* interpretation function and type of a boolean operation *)
let action_wrapper_boolop action a b error_infos s =
  match (a, b) with
  | FBool x, FBool y -> 
    FBool (action x y)
  | _ -> 
    raise (send_error 
             ("This boolean operation (" ^ s ^ ") only works on booleans")
             error_infos)

let type_checker_boolop  =
  Types.Fun(Types.Bool, Types.Fun(Types.Bool, Types.Bool))

(* interpretation function and type of a reflet *)
let action_reflet a b error_infos s =
  match (a) with 
  | FRef(x) -> 
    x := b; FUnit
  | _ -> 
    raise (send_error "Can't set a non ref value" error_infos)

let type_checker_reflet  = 
  let new_type = Types.Generic (Types.new_generic_id ())
  in Types.Fun(Types.Ref(new_type), Types.Fun(new_type, Types.Unit))


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
