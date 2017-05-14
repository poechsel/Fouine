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

let buildins_activated = ref true

module SubEnv =
struct 
  module E = Map.Make(struct
      type t = string
      let compare = Pervasives.compare
    end)

  type ('a) t = {imported: string list list; 
                 mem: 'a E.t; 
                 types: Expr.type_listing E.t; 
                 user_defined_types: (identifier * int * (type_listing list * user_defined_types)) list}

  let create = {imported = [[]];
                mem = E.empty; 
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
      | Module_type l ->
        { map with user_defined_types = (key, next_id, (parameters, Module_sig_decl l)) :: map.user_defined_types}
      | Basic_type t ->
        { map with user_defined_types = (key, next_id, (parameters, Renamed_decl (_update_types_pointer map t))) :: map.user_defined_types}
      | Constructor_list l ->
        let next_type = Called_type(key, next_id, parameters) in
        let map = { map with user_defined_types = (key, next_id, (parameters, Sum_decl next_type)) :: map.user_defined_types}
        in List.fold_left (
          fun a b ->
            match b with
            | Constructor_type (name, _, args) ->
              let args = match args with
                | None -> None
                | Some x -> Some (_update_types_pointer a x)
              in let next_id_constr = _find_latest_userdef a name 0
              in { a with user_defined_types = (name, next_id_constr, (parameters, Constructor_decl(Constructor_type(name, next_type, args)))) :: a.user_defined_types}
            | _ -> failwith "waited for a constructor"
        ) map l
          end
      | _ -> failwith "waited for a type declaration"

  let remove_tr_memory env name =
    let name = "tr_memory" in
    let env = if E.mem name env.mem then
        { env with mem = E.remove name env.mem}
      else env
    in if E.mem name env.types then
        { env with types = E.remove name env.types}
      else env


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

let rec list_of_array ar =
  let rec aux i =
    if i = Array.length ar then
      []
    else
      ar.(i) :: aux (i+1)
  in aux 0

module File =
  struct
    let search_max_depth = ref 4

    let is_hidden file_name =
      String.length file_name >= 1 && file_name.[0] == '.'

    let concat p f = p ^ "/" ^ f

    type result = None | Found of string

    let explode_file file_name =
      let count = ref 0 
      in let _ = String.iter (fun c -> if c = '.' then incr count) file_name
      in match !count with
      | 1 -> let pos = String.index file_name '.' 
        in (String.sub file_name 0 pos,
            String.sub file_name (pos+1) (String.length file_name - pos - 1))
      | _ -> ("", "")

    let get_visible path obj_list =
      List.filter (fun a -> not (is_hidden a)) obj_list
    let get_explorable_folders path obj_list =
      List.filter (fun n -> Sys.is_directory (concat path n)) obj_list
    let get_fouine_files path obj_list = 
      List.filter (fun n -> if Sys.is_directory (concat path n) then false else let (a, e) = explode_file n in e = "fo") obj_list

    let rec explore target path depth =
      let rec aux fifo = 
        match fifo with
        | [] -> None
        | (path, depth)::tl when depth > !search_max_depth -> None
        | (path, depth)::tl ->
          let files = list_of_array @@ Sys.readdir path
          in let files = get_visible path files
          in let folders = get_explorable_folders path files
          in let fouine = get_fouine_files path files
          in begin try
              Found (concat path (List.find (fun name -> let _ = print_endline  @@ path ^ " "^name in let name = String.uncapitalize name 
                                 in let (name, _) = explode_file name
                                 in name = target)
                       fouine))
            with Not_found -> 
              aux (tl @ List.map (fun a -> (concat path a, depth+1)) folders)
          end
      in aux [(".", 0)]
      (*
      let _ = print_endline @@ "======" ^ path in
      if depth > !search_max_depth then None
      else 
        let files = list_of_array @@ Sys.readdir path
        in let files = get_visible path files
        in let folders = get_explorable_folders path files
        in let fouine = get_fouine_files path files
        in begin try
               Found (List.find (fun name -> let _ = print_endline name in let name = String.uncapitalize name 
                           in let (name, _) = explode_file name
                           in name = target)
                        fouine)
          with Not_found ->
            let rec aux l = match l with
              | [] -> None
              | x::tl -> let r = explore target (concat path x) (depth+1)
                in match r with | None -> aux tl | r -> r
            in aux folders
        end
*)
    let rec seek_module name =
      let  _ = print_endline "new search [[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]" in
      let result = explore (String.uncapitalize name) "." 0
      in match result with
        | Found p -> p
        | _ -> raise Not_found


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

  type 'a t = string list * 'a sub_element




  let create = let temp = E.empty
    in ([], (Node (E.add "pervasive" (Node(E.empty, SubEnv.create)) temp, SubEnv.create)))

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




  let rec get_corresponding_subenv env (path_key, id) fct =
    (*let lyon_ = show_all_fouine_files () in *)
    let path, subenv_lists = env
    in let rec aux path subenv = match (path, subenv) with
        | [], Node (sub, env) -> fct env ([], id)
        | x :: t, Node(sub, env) -> 
          (*let _ = print_endline "content" in
            let _ = E.iter (fun a _ -> print_endline a) sub in *)
          if E.mem x sub then aux t (E.find x sub)
          else let _ = print_endline "failed" (*print_endline "env: " ; E.iter (fun a _ -> print_endline a) *)
            in raise Not_found
    in let rec test_paths path = 
         match path with
         | [] -> aux (List.rev path_key) subenv_lists
         | x::tl ->        
           begin try
               let _ = print_endline @@ "found" ^ (List.fold_left (fun a b -> a ^ " "^b) "" (List.rev (path_key @ path))) in
               aux (List.rev (path_key @ path)) subenv_lists
             with _ ->
               test_paths tl
           end
    in begin try 
        test_paths path
      with Not_found ->
        if List.length path_key = 0 then raise Not_found
        else 
          let _, Node(subenv, _) = env
          in let _ = E.iter (fun a b -> Printf.printf "%s " a) subenv
          in if E.mem (List.hd path_key) subenv then raise Not_found
          else
        let _ = print_endline "dynamic loading" in 
        let path = File.seek_module (List.hd path_key)
        in let _ = print_endline path
        in raise (LoadModule (List.hd path_key, path))
    end

  let rec add_corresponding_subenv env fct  =
    let path_current, subenv_lists = env
    in let rec aux path subenv = 
         let _ = print_endline @@ "adding " ^ List.fold_left (fun a b -> a ^ " " ^ b) "" path
         in match (path, subenv) with
        | [], Node (sub, env) ->  Node(sub, fct env)
        | x :: t, Node(sub, env) -> 
          let _ = E.iter (fun a _ -> print_endline a) sub in 
          if E.mem x sub then Node(E.add x (aux t (E.find x sub)) sub, env)
          else let _ = E.iter (fun a _ -> print_endline a) 
            in failwith  @@ x ^ " module not present " 
    in path_current, aux (List.rev path_current) subenv_lists

  let enter_module env name =
    let p, e = env in
    name :: p, e
  let quit_module env name =
    let _::p, e = env in
    p, e

  let create_module env name =
    let path_current, subenv_lists = env
    in let rec aux path subenv = match (path, subenv) with
        | [], Node (sub, env) -> Node(E.add name (Node(E.empty, SubEnv.create)) sub, env)
        | x :: t, Node(sub, env) -> if E.mem x sub then Node(E.add x (aux t (E.find x sub)) sub, env) 
          else  failwith  @@ x ^ " module not present " 
    in path_current, aux (List.rev path_current) subenv_lists



  let get_corresponding_id map what =
    let Called_type(name, i, l) = what in 
    get_corresponding_subenv map name (fun env name -> SubEnv.get_corresponding_id env (Called_type(name, i, l)))

  let get_latest_userdef map name id params =
    get_corresponding_subenv map name (fun env name -> SubEnv.get_latest_userdef env name id params)

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

  (*
  let remove_tr_memory map key = 
  let _ = disp map in
    let map  = add_corresponding_subenv map (fun env -> SubEnv.remove_tr_memory env key)
  in let _ = disp map
  in map
*)

  (*
  type 'a t = 'a SubEnv.t

  let create = SubEnv.create


  let get_corresponding_id map what =
    SubEnv.get_corresponding_id map what

  let get_latest_userdef map name id params =
    SubEnv.get_latest_userdef map name id params

  let add_userdef map new_type =
    SubEnv.add_userdef map new_type

  let mem map key =
    SubEnv.mem map key
  let remove map key = 
    SubEnv.remove map key
  let add map key prog =
    SubEnv.add map key prog
  let get_most_recent map key = 
    SubEnv.get_most_recent map key
  let add_type map key t =
    SubEnv.add_type map key t
  let mem_type map key = 
    SubEnv.mem_type map key
  let get_type map key = 
    SubEnv.get_type map key
    *)

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
      | x::tl, y::tl' when ast_equal x y -> aux tl tl'
      | x::tl, y::tl' when ast_slt x y -> true
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
