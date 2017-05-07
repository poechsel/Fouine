open Prettyprint
open Expr
open Shared
open Errors
open Lexing


(* check wether a polymorphic type var is included in the type t 
   If this is the case, we are wanting to unify 'a something like 'a, which isn't good at all
*)
let occurs var t =
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
    | Called_type (_, _, l) -> List.iter aux l
    | Ref_type l -> aux l
    | Array_type l -> aux l
    | Constructor_type (_, l, Some l') -> aux l; aux l'
    | Constructor_type (_, l, None) -> aux l
    | _ -> ()
  in aux t

(* instanciates a type, ie convert a type where all polymorphic types are fixed
   to a type where they can be changed 
   For use during unification
*)
let instanciate_with_tbl env tbl t level =
  let rec aux t =
    match t with 

    | Constructor_type(name, a, Some b) -> Constructor_type (name, aux a, Some (aux b))
    | Constructor_type(name, a, None) -> Constructor_type (name, aux a, None)
    | Generic_type i -> 
      if Hashtbl.mem tbl i then
        Hashtbl.find tbl i
      else
        let u = new_var level
        in let _ = Hashtbl.add tbl i u
        in u
    | Var_type {contents = Link x} -> aux x
    | Fun_type (t1, t2) -> Fun_type (aux t1, aux t2)
    | Called_type(name, id, l) ->   
      Env.get_corresponding_id env (Called_type(name, id, List.map aux l))
    | Tuple_type l -> Tuple_type (List.map aux l)
    | Ref_type l -> Ref_type (aux l)
    | Array_type l -> Array_type (aux l)
    | t -> t
  in aux t

let instanciate env t level =
  let tbl = Hashtbl.create 0
  in instanciate_with_tbl env tbl t level

(* unify two types.
   Almost all of this function is straightforward, except for 
   the part when whe check if a variable occurs in a type. This
   must be done because unifying 'a with 'a is impossible
*)
let unify env level t1 t2 =
  let rec unify t1 t2 =
    if t1 == t2 then ()
    else match (t1, t2) with
      | Fun_type (a, b), Fun_type (a', b') -> unify a a'; unify b b'
      | Tuple_type l, Tuple_type l' -> List.iter2 unify l l'
      | Ref_type x, Ref_type x' -> unify x x'
      | Array_type x, Array_type x' -> unify x x'

      | Called_type(name, id, l), Called_type(name', id', l') when name = name' && id = id' && List.length l = List.length l' -> List.iter2 unify l l'

      | Constructor_type(name, l, None), Constructor_type(name', l', None)  when name = name' ->
        unify l l'
      | Constructor_type(name, a, Some b), Constructor_type(name', a', Some b') when name = name' ->
        unify a a'; unify b b'
      | Var_type {contents = Link t1}, t2
      | t1, Var_type {contents = Link t2} -> unify t1 t2
      | Var_type ({contents = Unbound _} as tv),t'
      | t', Var_type ({contents = Unbound _} as tv) -> occurs tv t'; tv := Link t'

      | y, (Called_type (name, id, params) as x) 
      | (Called_type (name, id, params) as x), y ->
        let (x_type, x_repr) = begin try 
            Env.get_latest_userdef env name id params
          with Not_found ->
            raise (send_inference_error Lexing.dummy_pos (Printf.sprintf "Type %s not found" (string_of_ident name)))
        end
        in let tbl = Hashtbl.create 1
        in let (x_type, x_repr) = instanciate_with_tbl env tbl x_type level, instanciate_with_tbl env tbl x_repr level
        in let _ = unify x_type x
        in unify x_repr y
      | _, _ -> raise (InferenceError (UnificationError (Printf.sprintf "Can't unify type %s with type %s" (print_type t1) (print_type t2))))
  in unify t1 t2


(* generalize a type, ie convert a type where all polymorphic types can be changed
   to a type where they are fixed.
   For storage*)
let generalize t level = 
  let rec gen t =
    match t with
    | Called_type (name, id, l) -> Called_type (name, id, List.map gen l)
    | Constructor_type(name, a, Some b) -> Constructor_type (name, gen a, Some (gen b))
    | Constructor_type(name, a, None) -> Constructor_type (name, gen a, None)
    | Var_type {contents = Unbound (name,l)} 
      when l > level -> Generic_type name
    | Var_type {contents = Link ty} -> gen ty
    | Fun_type (t1, t2) -> Fun_type  (gen t1, gen t2)
    | Tuple_type l -> Tuple_type (List.map gen l)
    | Ref_type l -> Ref_type (gen l)
    | Array_type l -> Array_type (gen l)
    | t -> t
  in gen t





(* deal with errors due to binary operators.
   It is a big chunk of code, it goes here in consequence *)
let binop_errors binop_type env (a, a_type) (b, b_type) symbol node error_infos =
  match binop_type with
  | Fun_type (a_th_type, Fun_type (b_th_type, _)) ->
    let _ = try
        unify env 0 a_th_type a_type 
      with InferenceError (UnificationError _) ->
        let msg = Printf.sprintf "Operator %s, left argument: can't match type %s with type %s\n    in expression: %s" (symbol) (print_type b_th_type) (print_type b_type) (print_binop node "                 " true false)
        in raise (send_inference_error error_infos msg)
    in let _ = try
           unify env 0 b_th_type b_type
         with InferenceError (UnificationError _) ->
           let msg = Printf.sprintf "Operator %s, right argument: can't match type %s with type %s\n    in expression: %s" (symbol) (print_type b_th_type) (print_type b_type) (print_binop node "                 " false true)
           in raise (send_inference_error error_infos msg)
    in raise (InferenceError (Msg ("a boolean operator was coded in wrong format")))
  | _ -> raise (send_inference_error error_infos "This binary op didnt' have a correct type")




(* check if a list is made of unique elements *)
let list_has_unique_elements l =
  let rec aux l l' = List.length l = List.length l'
  in aux (List.sort_uniq compare l) l

let get_constructor_definition env name error_infos level =   
  try    
    let _, x = Env.get_latest_userdef env name (-1) [] in
    instanciate env x level 
  with Not_found -> 
    raise (send_inference_error error_infos (Printf.sprintf "Constructor %s not defined" (string_of_ident name))) 

(* get the type of a constructor *)
let get_constructor_type env name error_infos level =
  match (get_constructor_definition env name error_infos level) with  
  | Constructor_type (_, a, Some _) -> a  
  | Constructor_type (_, a, None) -> a   | _ -> failwith "how am I supposed to get the type of a constructor if I don't have a constructor?" 


(* compute the type of (and check inference)
   of a pattern.
   It also allocates the types of symboles
    (for exemple, in the pattern (x, 2, y) it will
   allocates the type of x and y)
*)
let rec type_pattern_matching expr t level env = 
  match expr with
  | Underscore -> env
  | Ident (name, _) -> 
    let new_type = match t with
      | Ref_type _ -> t
      | _ -> generalize t level
    in Env.add_type env name new_type
  | FixedType (x, t', error) -> 
    begin
      try
        let t' = instanciate env t' level in
        let _ = Printf.printf "infering inside matching\n   %s vs %s\n" (print_type t') (print_type t) in
        let env = type_pattern_matching x t' level env
        in let _ = unify env level t t'
        in env

      with InferenceError (UnificationError m) ->
        raise (send_inference_error error m)
    end
  | Const _ -> unify env level Int_type t; env
  | Bool _ -> unify env level Bool_type t; env
  | Unit -> unify env level Unit_type t; env
  | Tuple (l, _) ->
    let new_types = List.map (fun _ -> new_var level) l
    in let _ = unify env level (Tuple_type new_types) t
    in let rec aux l l_types env =
         match (l, l_types) with 
         | [], [] -> env
         | x::l, x_type::l' -> aux l l' @@ type_pattern_matching x x_type level env
         | _ -> failwith "this wasn't suppose to happen"
    in aux l new_types env

  | Constructor (name, None, error_infos) ->
    unify env level (get_constructor_type env name error_infos level) t;
    env
  | Constructor (name, Some expr, error_infos) ->
    let constructeur = get_constructor_definition env name error_infos level
    in begin match constructeur with
      | Constructor_type (_, arg, Some type_expr) ->
        let _ = unify env level t arg
        in type_pattern_matching expr type_expr level env
      | _ -> failwith "ouspi"
    end


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
            let _ = Printf.printf "infering here\n" in
            let t' = instanciate env t' level
            in let env, t = inference x env level
            in let _ = unify env level t t'
            in env, t'
          with InferenceError (UnificationError m) ->
            raise (send_inference_error error m)
        end
      | Ident(name, error_infos) ->
        begin
          try
            env, instanciate env (Env.get_type env name) level
          with Not_found ->
            raise (send_inference_error error_infos ("identifier '" ^ string_of_ident name ^ "' not found"))
        end

      | Constructor (name, None, error_infos) ->
        let def = get_constructor_definition env name error_infos level
        in begin
          try
            let u = new_var level 
            in let _ = unify env level (Constructor_type(name, u, None)) def
            in env, u
          with InferenceError (UnificationError m)->
            begin
              match def with
              | Constructor_type (_, _, Some l) ->
                raise (send_inference_error error_infos "expected a constructor with arguments")
              | _ ->
                raise (send_inference_error error_infos m) 
            end
        end


      | Constructor(name, Some arg, error_infos) 
      | Call(Constructor (name, None, _), arg, error_infos) ->
        let def = get_constructor_definition env name error_infos level
        in let _, t_arg = inference arg env level
        in begin
          try
            let u = new_var level
            in let _ = unify env level (Constructor_type(name, u, Some t_arg)) def 
            in env, u
          with InferenceError (UnificationError m)->
            begin
              match def with
              | Constructor_type (_, _, None) ->
                raise (send_inference_error error_infos "expected a constructor without arguments")
              | Constructor_type (_, _, Some l) ->
                raise (send_inference_error error_infos (Printf.sprintf "argument was expected to have type %s but had type %s" (print_type l) (print_type t_arg)))
              | _ -> failwith "bad type"
            end
        end


      | TypeDecl (id, l, error_infos) ->
        Env.add_userdef env expr, Unit_type
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
        in type_pattern_matching pattern type_expr level env, instanciate env type_expr level

      | LetRec((Ident (name, _)), expr, _) ->
        let env' = Env.add_type env name ((new_var (level+1)))
        in let type_expr = snd @@ inference expr env' (level + 1)
        in let _ = unify env level type_expr ((Env.get_type env' name))
        in let env'' = Env.add_type env' name (generalize type_expr level)
        in env'', Env.get_type env'' name

      | In(Let(pattern, expr, _), next, _) ->
        let type_expr = snd @@ inference expr env (level + 1)
        in inference next (type_pattern_matching pattern type_expr level env) level

      | In(LetRec((Ident (name, _)), expr, _), next, _) ->
        let env' = Env.add_type env name (new_var (level+1))
        in let type_expr = snd @@ inference expr env' (level + 1)
        in let _ = unify env level type_expr (Env.get_type env' name)
        in let env'' = Env.add_type env' name (generalize (type_expr) level)
        in inference next env'' level

      | IfThenElse(cond, if_expr, else_expr, error_infos) ->
        let _, cond_type = inference cond env level
        in let _ = try unify env level cond_type Bool_type
             with InferenceError (UnificationError _) ->
               raise (send_inference_error error_infos (Printf.sprintf "A condition must have type bool, here it is having type %s" (print_type cond_type)))
        in let _, if_expr_type = inference if_expr env level
        in let _, else_expr_type = inference else_expr env level
        in let _ = try 
               unify env level if_expr_type else_expr_type
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
            let _ = unify env level fun_type (Fun_type (arg_type, out_type))
            in env, out_type
          with InferenceError (UnificationError m) ->
          match fun_type with
          | Fun_type (arg_th_type, _) -> raise (send_inference_error error_infos (Printf.sprintf "function as argument of type %s, but here it is called with type %s" (print_type arg_th_type) (print_type arg_type)))
          | _ -> raise (send_inference_error error_infos (Printf.sprintf "Calling function with too much arguments: %s %s" m (pretty_print expr)))
        end

      | BinOp(x, a, b, t) ->
        let _, b_type = inference b env level
        in let _, a_type = inference a env level
        in let comp_type = instanciate env (x#type_check) level
        in let out_type = new_var level
        in begin try
            let _ = unify env level comp_type (Fun_type(a_type, Fun_type (b_type, out_type)))
            in env, out_type
          with InferenceError (UnificationError _) ->
            binop_errors comp_type env (a, a_type) (b, b_type) x#symbol expr t
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
                unify env level a b;b
              with InferenceError (UnificationError _)->
                raise (send_inference_error errors (Printf.sprintf "can't unify env level %s and %s in pattern matching" (print_type a) (print_type b)))   
            end   ) match_expr_type pattern_types
        in env, List.fold_left (fun a b -> begin
              try
                unify env level a b;b
              with InferenceError (UnificationError _) ->
                raise (send_inference_error errors (Printf.sprintf "Can't unify env level expressions in matching. Should it return %s or %s?" (print_type a) (print_type b)))
            end )
            (List.hd action_types) (List.tl action_types)

      | Raise (e, error_infos) ->
        let _, t = inference e env level
        in let _ = unify env level t Int_type
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
               unify env level type_try type_with
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
        in let _ = unify env level t (Ref_type n)
        in env, n

      | ArraySet (id, expr, nvalue, error_infos) ->
        let _, th = inference (ArrayItem(id, expr, error_infos)) env level
        in let _, tvalue = inference nvalue env level
        in let _ = begin try 
               unify env level th tvalue 
             with InferenceError (UnificationError _) ->
               raise (send_inference_error error_infos (Printf.sprintf "Can't affect an expression of type %s to an element of a %s.\n  In expression: %s" (print_type tvalue) (print_type th) (pretty_print_arrayset expr "" true true)))
           end 
        in env, Unit_type

      | ArrayItem (id, expr, error_infos) ->
        let u = new_var level
        in let _ = begin try 
               unify env level (Array_type u) (snd @@ inference id env level)
             with InferenceError (UnificationError _ ) ->
               raise (send_inference_error error_infos (Printf.sprintf "expression %s is not representing an array" (pretty_print_arrayitem expr "" true true false)))
           end 
        in let _ =  begin try 
               unify env level u (snd @@ inference expr env level)
             with InferenceError (UnificationError _ ) ->
               raise (send_inference_error error_infos (Printf.sprintf "Can't suscribe to the array. The index isn't an int.\n  In expression: %s" (pretty_print_arrayitem expr "" true false true)))
           end in
        env, u



      (* now the buildins - printin, not, amake, .... *)
      | ArrayMake (expr, t) -> begin
          let _, arg_type = inference expr env level
          in try
            let _ = unify env level arg_type Int_type
            in env, Array_type Int_type
          with InferenceError (UnificationError m) ->
            raise (send_inference_error t (Printf.sprintf "aMake constructor requires a int argument, not a %s.\n  In expression: %s" (print_type arg_type) (pretty_print_amake expr "  " true true)))
        end
      | Not (expr, t) -> begin
          let _, arg_type = inference expr env level
          in try
            let _ = unify env level arg_type Bool_type
            in env, Bool_type
          with InferenceError (UnificationError m) ->
            raise (send_inference_error t (Printf.sprintf "Not function requires a bool argument, not a %s.\n  In expression: %s" (print_type arg_type) (pretty_print_amake expr "  " true true)))
        end

      | Printin (expr, t) -> begin
          let _, arg_type = inference expr env level
          in try
            let _ = unify env level arg_type Int_type
            in env, Int_type
          with InferenceError (UnificationError m) ->
            raise (send_inference_error t (Printf.sprintf "prInt constructor requires a int argument, not a %s.\n  In expression: %s" (print_type arg_type) (pretty_print_prInt expr "  " true true)))
        end

      | _ -> failwith @@ "Encoutered something we can't infer:" ^ show_expr expr
    in e, t

  in inference expr env 0
