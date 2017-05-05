open Prettyprint
open Expr
open Shared
open Errors
open Lexing


(* check wether a polymorphic type var is included in the type t 
   If this is the case, we are wanting to unify 'a something like 'a, which isn't good at all
*)
let occurs var t =
  let _ = print_endline " zioenr"in
  let rec aux t =
    match t with
    | Var_type x when !x = !var -> 
      raise (InferenceError (Msg (Printf.sprintf "Unification error. Can't unify these two types: %s because one occurs in the other" (print_type_duo (Var_type var) t))))
    | Var_type x -> begin
        (* this part is because variables are nested to a level: when seeing to variable
           at different levels, the higher level one must be unyfied with the lower level one *)
        match !x with
        | Unbound (id', l') ->
          let min_level = match !var with | Unbound(_, l) -> min l l' | _ -> l'
          in x := Unbound (id', min_level)
        | Link t -> aux t
      end
    | Fun_type (t1, t2) -> aux t1;aux t2
    | Tuple_type l -> List.iter aux l
    | Called_type (_,l) -> List.iter aux l
    | Ref_type l -> aux l
    | Array_type l -> aux l
    | Constructor_type (_, l, l') -> aux l; aux l'
    | Constructor_type_noarg (_, l) -> aux l
    | _ -> ()
  in aux t


(* unify two types.
   Almost all of this function is straightforward, except for 
   the part when whe check if a variable occurs in a type. This
   must be done because unifying 'a with 'a is impossible
*)
let unify t1 t2 =
(*  let _ = Printf.printf ("unify %s with %s\n") (print_type t1) (print_type t2)
      in*)
  let rec unify t1 t2 =
    if t1 == t2 then ()
    else match (t1, t2) with

      | Fun_type (a, b), Fun_type (a', b') -> unify a a'; unify b b'
      | Tuple_type l, Tuple_type l' -> List.iter2 unify l l'
      | Ref_type x, Ref_type x' -> unify x x'
      | Array_type x, Array_type x' -> unify x x'

      | Called_type(name, l), Called_type(name', l') when name = name' -> List.iter2 unify l l'
      | Constructor_type_noarg(name, l), Constructor_type_noarg(name', l')  when name = name' ->
        unify l l'
      | Constructor_type(name, a, b), Constructor_type(name', a', b') when name = name' ->
        unify a a'; unify b b'
      | Var_type {contents = Link t1}, t2
      | t1, Var_type {contents = Link t2} -> unify t1 t2
      | Var_type ({contents = Unbound _} as tv),t'
      | t', Var_type ({contents = Unbound _} as tv) -> occurs tv t'; tv := Link t'

      | _, _ -> raise (InferenceError (UnificationError (Printf.sprintf "Can't unify type %s with type %s" (print_type t1) (print_type t2))))
  in unify t1 t2


(* generalize a type, ie convert a type where all polymorphic types can be changed
   to a type where they are fixed.
   For storage*)
let generalize t level = 
  let rec gen t =
    match t with
    | Called_type (name, l) -> Called_type (name, List.map gen l)
    | Constructor_type(name, a, b) -> Constructor_type (name, gen a, gen b)
    | Constructor_type_noarg(name, a) -> Constructor_type_noarg (name, gen a)
    | Var_type {contents = Unbound (name,l)} 
      when l > level -> Generic_type name
    | Var_type {contents = Link ty} -> gen ty
    | Fun_type (t1, t2) -> Fun_type  (gen t1, gen t2)
    | Tuple_type l -> Tuple_type (List.map gen l)
    | Ref_type l -> Ref_type (gen l)
    | Array_type l -> Array_type (gen l)
    | t -> t
  in gen t

(* instanciates a type, ie convert a type where all polymorphic types are fixed
   to a type where they can be changed 
   For use during unification
*)
let instanciate t level =
  let tbl = Hashtbl.create 0
  in let rec aux t =
       match t with 
       | Constructor_type(name, a, b) -> Constructor_type (name, aux a, aux b)
       | Constructor_type_noarg(name, a) -> Constructor_type_noarg (name, aux a)
       | Generic_type i -> 
         if Hashtbl.mem tbl i then
           Hashtbl.find tbl i
         else
           let u = new_var level
           in let _ = Hashtbl.add tbl i u
           in u
       | Var_type {contents = Link x} -> aux x
       | Fun_type (t1, t2) -> Fun_type (aux t1, aux t2)
       | Called_type(name, l) -> Called_type(name, List.map aux l)
       | Tuple_type l -> Tuple_type (List.map aux l)
       | Ref_type l -> Ref_type (aux l)
       | Array_type l -> Array_type (aux l)
       | t -> t
  in aux t




(* deal with errors due to binary operators.
   It is a big chunk of code, it goes here in consequence *)
let binop_errors binop_type (a, a_type) (b, b_type) symbol node error_infos =
  match binop_type with
  | Fun_type (a_th_type, Fun_type (b_th_type, _)) ->
    let _ = try
        unify a_th_type a_type 
      with InferenceError (UnificationError _) ->
        let msg = Printf.sprintf "Operator %s, left argument: can't match type %s with type %s\n    in expression: %s" (symbol) (print_type b_th_type) (print_type b_type) (print_binop node "                 " true false)
        in raise (send_inference_error error_infos msg)
    in let _ = try
           unify b_th_type b_type
         with InferenceError (UnificationError _) ->
           let msg = Printf.sprintf "Operator %s, right argument: can't match type %s with type %s\n    in expression: %s" (symbol) (print_type b_th_type) (print_type b_type) (print_binop node "                 " false true)
           in raise (send_inference_error error_infos msg)
    in raise (InferenceError (Msg ("a boolean operator was coded in wrong format")))
  | _ -> raise (send_inference_error error_infos "This binary op didnt' have a correct type")




(************************************************************
            Type Declaration
 *************************************************************)
(* check if a list is made of unique elements *)
let list_has_unique_elements l =
  let rec aux l l' = List.length l = List.length l'
  in aux (List.sort_uniq compare l) l

(* the two following functions are here two deal with types overlapping
   It is useful when two types having the same name are defined:
   type test = None of test
   type test = Foo of test
   We want Foo to refers to the second test and None to the first one

   We are using a small trick:
   An type name is padded with spaces (non parsed character) at the begin, and the number of spaces is equal to the number
   of types of the same name already introduced. This simulates stacking *)

(* find the transformed name for a type *)
let rec find_next_type_name name env = 
  let name = " " ^ name
  in if Env.mem_type env name then
    find_next_type_name name env
  else 
    name

(* find the most recent occurence of a type name (ie we
   pad it with spaces until we find nothing, the last one
   existing is the newest created type having this name)
*)
let rec find_last_type_name name env =
  let name = " " ^ name in
  if Env.mem_type env  name then
    let t = find_last_type_name name env
    in if t = "" then name else t
  else ""

(* check if two types are compatible
   (ie if they have the same number of arguments *)
let check_compatibility_types t1 t2 error =
  match (t1, t2) with 
  | Called_type (name, l), Called_type (name', l') ->
    if name = name' then
      let ll = List.length l
      in let ll' = List.length l'
      in if ll = ll' then true
      else 
        raise (send_inference_error error (Printf.sprintf "not enough argument for type %s: expecting %d arguments, got %d" name ll ll'))
    else 
      failwith "strange"

  | _ -> failwith "bad arguments"

(* updates the subtypes in declaration to link them
   to the last seen types

   In the previous exemple with test's, when declaring Foo, we when its
   occurence of test to point in direction of the last declared test type
*)
let rec update_subtypes_name type_name new_type env error t =
  let aux = update_subtypes_name type_name new_type env error in
  match t with
  | Tuple_type l -> Tuple_type (List.map aux l)
  | Constructor_type (a, b, l) -> Constructor_type (a, aux b, aux l)
  | Constructor_type_noarg(a, b) -> Constructor_type_noarg(a, aux b)
  | Ref_type x                  -> Ref_type (aux x)
  | Array_type l                -> Array_type (aux l)
  | Arg_type x                  -> Arg_type (aux x)
  | Fun_type (a, b)             -> Fun_type (aux a, aux b)
  | Called_type (name, l)       ->
    let new_name = find_last_type_name name env
    in if type_name = name then
      if check_compatibility_types new_type t error then
        if new_name = "" then
          Called_type (" " ^ name, l)
        else 
          Called_type (" " ^ new_name, l)
      else failwith "ouspi"
    else
    if new_name = "" then
      raise (send_inference_error error (Printf.sprintf "incorrect identifier %s" name))
    else if check_compatibility_types (Env.get_type env new_name) t error then 
      Called_type(new_name, l)
    else failwith "oupsi"
  | _ -> t


let analyse_basic_type_declaration new_type content error env level =
  match new_type with 
  | Called_type (name_type, parametrization) ->
    let _ = print_endline "aze" in
    if list_has_unique_elements parametrization then
      let name_new_type = find_next_type_name name_type env
      in let called_type = generalize (Called_type (name_new_type, parametrization)) level
      in let called_type = (generalize (update_subtypes_name name_type new_type env error content) level)
      in let _ = print_type called_type 
      in Env.add_type env name_new_type called_type, called_type
    else 
      raise (send_error "You have a duplicate polymorphic type in this declaration" error)
  | _ -> raise (send_error "Waited for an expr name" error)

(* finally, we analyse a type declaration:
   we check if in the definition name all parameters are unique:
    type ('a, 'a) test is invalid for exemple
   We also iterates through constructors in order to analyse their types (see the previous function )
*)
let analyse_type_declaration new_type constructor_list error env level =
  match new_type with 
  | Called_type (name_type, parametrization) ->
    if list_has_unique_elements parametrization then
      let name_new_type = find_next_type_name name_type env
      in let called_type = generalize (Called_type (name_new_type, parametrization)) level
      in let type_constructor env constructor =
           match constructor with
           | Constructor_type_noarg (constr_name, _) ->
             let temp = Constructor_type_noarg (constr_name, called_type)
             in Env.add_type env constr_name temp
           | Constructor_type (constr_name, _, expr) ->
             let temp = Constructor_type (constr_name, called_type, generalize (update_subtypes_name name_type new_type env error expr) level)
             in Env.add_type env constr_name temp
           | _ -> failwith (print_type constructor)
      in let env = List.fold_left type_constructor env constructor_list
      in Env.add_type env name_new_type called_type, called_type
    else 
      raise (send_error "You have a duplicate polymorphic type in this declaration" error)
  | _ -> raise (send_error "Waited for an expr name" error)
(*************************************************************)


(* get the definition of a Constructor
   Deals with errors *)
let get_constructor_definition env name error_infos level =
  try
    instanciate (Env.get_type env name) level
  with Not_found ->
    raise (send_inference_error error_infos (Printf.sprintf "Constructor %s not defined" name))

(* get the type of a constructor *)
let get_constructor_type env name error_infos level =
  match (get_constructor_definition env name error_infos level) with
  | Constructor_type (_, a, _) -> a
  | Constructor_type_noarg (_, a) -> a
  | _ -> failwith "how am I supposed to get the type of a constructor if I don't have a constructor?"


(* compute the type of (and check inference)
   of a pattern.
   It also allocates the types of symboles
    (for exemple, in the pattern (x, 2, y) it will
   allocates the type of x and y)
*)
let rec type_pattern_matching expr t level env = 
  match expr with
  | Underscore -> env
(*  | FixedType (Ident(name, _), t_name, _) -> 
    let _ = print_endline "inspecting food thig" in
    let new_type = generalize t_name level
    in Env.add_type env name new_type
*)  | Ident _ as name -> 
    let new_type = generalize t level
    in Env.add_type env (string_of_ident name) new_type
  | FixedType (x, t', error) -> 
    begin
      try
        let t' = instanciate t' level in
        let env = type_pattern_matching x t' level env
        in let _ = unify t t'
        in env

      with InferenceError (UnificationError m) ->
        raise (send_inference_error error m)
    end
  | Const _ -> unify Int_type t; env
  | Bool _ -> unify Bool_type t; env
  | Unit -> unify Unit_type t; env
  | Tuple (l, _) ->
    let new_types = List.map (fun _ -> new_var level) l
    in let _ = unify (Tuple_type new_types) t
    in let rec aux l l_types env =
         match (l, l_types) with 
         | [], [] -> env
         | x::l, x_type::l' -> aux l l' @@ type_pattern_matching x x_type level env
         | _ -> failwith "this wasn't suppose to happen"
    in aux l new_types env

  (*| Constructor_noarg (name, error_infos) ->
    unify (get_constructor_type env name error_infos level) t;
    env
  | Constructor (name, expr, error_infos) ->
    let constructeur = get_constructor_definition env name error_infos level
    in begin match constructeur with
      | Constructor_type (_, arg, type_expr) ->
        let _ = unify t arg
        in type_pattern_matching expr type_expr level env
      | _ -> failwith "ouspi"
    end
    *)
    
    | _ -> failwith "incorrect symbol encountered during pattern matching"



(* the type inference itself.
   It is just some boring steps using previous functions
   The code is horrific because we are also checking for
   errors
*)
let analyse expr env = 
  let  rec inference expr env level =
    let e, t = match expr with
      | Const _ -> env, Int_type
      | Bool _ -> env, Bool_type
      | Unit -> env, Unit_type
      | Underscore ->
        env, new_var level
      | FixedType (x, t', error) -> 
        begin
          try
            let env, t = inference x env level
            in let _ = unify t (instanciate t' level)
            in env, t
          with InferenceError (UnificationError m) ->
            raise (send_inference_error error m)
        end
      | Ident((_, name), error_infos) as i ->
        let name = string_of_ident i in
        begin
          try
            env, instanciate (Env.get_type env name) level
          with Not_found ->
            raise (send_inference_error error_infos ("identifier '" ^ name ^ "' not found"))
        end

      (*| Constructor_noarg (name, error_infos) ->
        let def = get_constructor_definition env name error_infos level
        in begin
          try
            let u = new_var level 
            in let _ = unify (Constructor_type_noarg(name, u)) def
            in env, u
          with InferenceError (UnificationError m)->
            begin
              match def with
              | Constructor_type (_, _, l) ->
                raise (send_inference_error error_infos "expected a constructor with arguments")
              | _ ->
                raise (send_inference_error error_infos m) 
            end
        end


      | Constructor(name, arg, error_infos) 
      | Call(Constructor_noarg (name, _), arg, error_infos) ->
        let def = get_constructor_definition env name error_infos level
        in let _, t_arg = inference arg env level
        in begin
          try
            let u = new_var level
            in let _ = unify (Constructor_type(name, u, t_arg)) def 
            in env, u
          with InferenceError (UnificationError m)->
            begin
              match def with
              | Constructor_type_noarg _ ->
                raise (send_inference_error error_infos "expected a constructor without arguments")
              | Constructor_type (_, _, l) ->
                raise (send_inference_error error_infos (Printf.sprintf "argument was expected to have type %s but had type %s" (print_type l) (print_type t_arg)))
              | _ -> failwith "bad type"
            end
        end
*)

      | TypeDecl (id, l, error_infos) ->
        env, Unit_type
        (*
        begin
          match l with
          | Constructor_list l ->
            analyse_type_declaration id l error_infos env level
          | Basic_type t ->let _ = print_endline "begin" in analyse_basic_type_declaration id t error_infos env level
        end
        *)
      | Tuple (l, _) ->
        env, Tuple_type (List.map (fun x -> snd (inference x env level)) l)

      | Let(pattern, expr, _) ->
        let type_expr = snd @@ inference expr env (level + 1)
        in type_pattern_matching pattern type_expr level env, instanciate type_expr level

      | LetRec((Ident _ as name), expr, _) ->
        let name = string_of_ident name in
        let env' = Env.add_type env name ((new_var (level+1)))
        in let type_expr = snd @@ inference expr env' (level + 1)
        in let _ = unify type_expr ((Env.get_type env' name))
        in let env'' = Env.add_type env' name (generalize type_expr level)
        in env'', Env.get_type env'' name

      | In(Let(pattern, expr, _), next, _) ->
        let type_expr = snd @@ inference expr env (level + 1)
        in inference next (type_pattern_matching pattern type_expr level env) level

      | In(LetRec((Ident _) as name, expr, _), next, _) ->
        let name = string_of_ident name in
        let env' = Env.add_type env name (new_var (level+1))
        in let type_expr = snd @@ inference expr env' (level + 1)
        in let _ = unify type_expr (Env.get_type env' name)
        in let env'' = Env.add_type env' name (generalize (type_expr) level)
        in inference next env'' level

      | IfThenElse(cond, if_expr, else_expr, error_infos) ->
        let _, cond_type = inference cond env level
        in let _ = try unify cond_type Bool_type
             with InferenceError (UnificationError _) ->
               raise (send_inference_error error_infos (Printf.sprintf "A condition must have type bool, here it is having type %s" (print_type cond_type)))
        in let _, if_expr_type = inference if_expr env level
        in let _, else_expr_type = inference else_expr env level
        in let _ = try 
               unify if_expr_type else_expr_type
             with InferenceError (UnificationError m) ->
               raise (send_inference_error error_infos m)
        in env, if_expr_type


      | Fun(args, expr, error_infos) ->
        let args_type = new_var level
        in let env' = type_pattern_matching args args_type level env
        in let _ = Printf.printf "decalring fun th: %s \n" (print_type args_type)
        in let _, out_type = inference expr env' level
        in env, Fun_type (args_type, out_type)

      | Call(expr, arg, error_infos) ->
        let _, fun_type = inference expr env level
        in let _, arg_type = inference arg env level
        in let out_type = new_var level
        in begin try
            let _ = unify fun_type (Fun_type (arg_type, out_type))
            in env, out_type
          with InferenceError (UnificationError m) ->
          match fun_type with
          | Fun_type (arg_th_type, _) -> raise (send_inference_error error_infos (Printf.sprintf "function as argument of type %s, but here it is called with type %s" (print_type arg_th_type) (print_type arg_type)))
          | _ -> raise (send_inference_error error_infos (Printf.sprintf "Calling function with too much arguments: %s %s" m (pretty_print expr)))
        end

      | BinOp(x, a, b, t) ->
        let _, b_type = inference b env level
        in let _, a_type = inference a env level
        in let comp_type = instanciate (x#type_check) level
        in let out_type = new_var level
        in begin try
            let _ = unify comp_type (Fun_type(a_type, Fun_type (b_type, out_type)))
            in env, out_type
          with InferenceError (UnificationError _) ->
            binop_errors comp_type (a, a_type) (b, b_type) x#symbol expr t
        end

      | Seq(a, b, _) | MainSeq(a, b, _) ->
        let env', _ = inference a env level
        in inference b env' level

      | MatchWith (match_expr, matches, errors) ->
        let _, match_expr_type = inference match_expr env level
        in let temp = List.map (fun (m, a) -> 
            let env' = type_pattern_matching m match_expr_type level env
            in match_expr_type, snd @@ inference a env' level)
            matches
        in let pattern_types, action_types = List.split temp
        in let _ = List.fold_left (fun a b -> begin
              try
                unify a b;b
              with InferenceError (UnificationError _)->
                raise (send_inference_error errors (Printf.sprintf "can't unify %s and %s in pattern matching" (print_type a) (print_type b)))   
            end   ) match_expr_type pattern_types
        in env, List.fold_left (fun a b -> begin
              try
                unify a b;b
              with InferenceError (UnificationError _) ->
                raise (send_inference_error errors (Printf.sprintf "Can't unify expressions in matching. Should it return %s or %s?" (print_type a) (print_type b)))
            end )
            (List.hd action_types) (List.tl action_types)

      | Raise (e, error_infos) ->
        let _, t = inference e env level
        in let _ = unify t Int_type
        in env, (new_var (level))

      | TryWith (try_clause, error, with_clause, error_infos) ->
        let _, type_try = inference try_clause env level
        in let env' = begin try

               type_pattern_matching error Int_type level env
             with InferenceError (UnificationError m) ->
               raise (send_inference_error error_infos m)
           end
        in let _, type_with = inference with_clause env' level
        in let _ = begin try
               unify type_try type_with
             with InferenceError  (UnificationError m)->
               raise (send_inference_error error_infos (Printf.sprintf "The two expression in a trywith clause must have the same type. Here: \n  First expression has type %s\n  Second expression has type %s" (print_type type_try) (print_type type_with)))
           end 
        in env, type_try


      | Ref (x, error_infos) ->
        let _, t = inference x env level
        in env, Ref_type t

      | Bang (x, error_infos) ->
        let _, t = inference x env level
        in let n = new_var level
        in let _ = unify t (Ref_type n)
        in env, n

      | ArraySet (id, expr, nvalue, error_infos) ->
        let _, th = inference (ArrayItem(id, expr, error_infos)) env level
        in let _, tvalue = inference nvalue env level
        in let _ = begin try 
               unify th tvalue 
             with InferenceError (UnificationError _) ->
               raise (send_inference_error error_infos (Printf.sprintf "Can't affect an expression of type %s to an element of a %s.\n  In expression: %s" (print_type tvalue) (print_type th) (pretty_print_arrayset expr "" true true)))
           end 
        in env, Unit_type

      | ArrayItem (id, expr, error_infos) ->
        let u = new_var level
        in let _ = begin try 
               unify (Array_type u) (snd @@ inference id env level)
             with InferenceError (UnificationError _ ) ->
               raise (send_inference_error error_infos (Printf.sprintf "expression %s is not representing an array" (pretty_print_arrayitem expr "" true true false)))
           end 
        in let _ =  begin try 
               unify u (snd @@ inference expr env level)
             with InferenceError (UnificationError _ ) ->
               raise (send_inference_error error_infos (Printf.sprintf "Can't suscribe to the array. The index isn't an int.\n  In expression: %s" (pretty_print_arrayitem expr "" true false true)))
           end in
        env, u



      (* now the buildins - printin, not, amake, .... *)
      | ArrayMake (expr, t) -> begin
          let _, arg_type = inference expr env level
          in try
            let _ = unify arg_type Int_type
            in env, Array_type Int_type
          with InferenceError (UnificationError m) ->
            raise (send_inference_error t (Printf.sprintf "aMake constructor requires a int argument, not a %s.\n  In expression: %s" (print_type arg_type) (pretty_print_amake expr "  " true true)))
        end
      | Not (expr, t) -> begin
          let _, arg_type = inference expr env level
          in try
            let _ = unify arg_type Bool_type
            in env, Bool_type
          with InferenceError (UnificationError m) ->
            raise (send_inference_error t (Printf.sprintf "Not function requires a bool argument, not a %s.\n  In expression: %s" (print_type arg_type) (pretty_print_amake expr "  " true true)))
        end

      | Printin (expr, t) -> begin
          let _, arg_type = inference expr env level
          in try
            let _ = unify arg_type Int_type
            in env, Int_type
          with InferenceError (UnificationError m) ->
            raise (send_inference_error t (Printf.sprintf "prInt constructor requires a int argument, not a %s.\n  In expression: %s" (print_type arg_type) (pretty_print_prInt expr "  " true true)))
        end

      | _ -> failwith @@ "Encoutered something we can't infer:" ^ show_expr expr
    in e, t

  in inference expr env 0
