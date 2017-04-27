open Prettyprint
open Expr
open Env
open Errors
open Lexing


let occurs var t =
  let rec aux t =
    match t with
    | Var_type x when !x = !var -> raise (InferenceError (Msg (Printf.sprintf "Unification error. Can't unify these two types: %s because one occurs in the other" (print_type (Params_type [Var_type var; t])))))
    | Var_type x -> begin
        match !x with
        | Unbound (id', l') ->
          let min_level = match !var with | Unbound(_, l) -> min l l' | _ -> l'
          in x := Unbound (id', min_level)
        | Link t -> aux t
      end
    | Fun_type (t1, t2) -> aux t1;aux t2
    | Tuple_type l -> List.iter aux l
    | Params_type l -> List.iter aux l
    | Ref_type l -> aux l
    | _ -> ()
  in aux t

let rec prune t =
  match t with
  | Var_type ({contents = Link x}) -> prune x
  | Fun_type (a, b) -> Fun_type (prune a, prune b)
  | Tuple_type l -> Tuple_type (List.map prune l)
  | Params_type l -> Params_type (List.map prune l)
  | Ref_type x -> Ref_type (prune x)
  | _ -> t


let rec unify t1 t2 =
  if t1 == t2 then ()
  else match (t1, t2) with
    | Var_type ({contents = Unbound _} as tv),t'
    | t', Var_type ({contents = Unbound _} as tv) -> occurs tv t'; tv := Link t'
    | Var_type {contents = Link t1}, t2
    | t1, Var_type {contents = Link t2} -> unify t1 t2

    | Fun_type (a, b), Fun_type (a', b') -> unify a a'; unify b b'
    | Params_type l, Params_type l' -> List.iter2 unify l l'
    | Tuple_type l, Tuple_type l' -> List.iter2 unify l l'
    | Ref_type x, Ref_type x' -> unify x x'

    | _, _ -> raise (InferenceError (UnificationError (Printf.sprintf "Can't unify type %s with type %s" (print_type t1) (print_type t2))))


let generalize t level = 
  let rec gen t =
  match t with
  | Var_type {contents = Unbound (name,l)} 
      when l > level -> Generic_type name
  | Var_type {contents = Link ty} -> gen ty
  | Fun_type (t1, t2) -> Fun_type  (gen t1, gen t2)
  | Params_type l -> Params_type (List.map gen l)
  | Tuple_type l -> Tuple_type (List.map gen l)
  | Ref_type l -> Ref_type (gen l)
  | t -> t
  in gen t

let instanciate t level =
  let tbl = Hashtbl.create 0
  in let rec aux t =
       match t with 
       | Generic_type i -> 
         if Hashtbl.mem tbl i then
           Hashtbl.find tbl i
         else
           let u = new_var level
           in let _ = Hashtbl.add tbl i u
           in u
       | Var_type {contents = Link x} -> aux x
       | Fun_type (t1, t2) -> Fun_type (aux t1, aux t2)
       | Params_type l -> Params_type (List.map aux l)
       | Tuple_type l -> Tuple_type (List.map aux l)
       | Ref_type l -> Ref_type (aux l)
       | _ -> t
  in aux t

let type_of_const const = 
  match const with
  | Const _ -> Int_type
  | Bool _ -> Bool_type
  | Unit -> Unit_type
  | _ -> failwith "not waited for this thing"


let rec type_pattern_matching expr t level env = 
  match expr with
  | Underscore -> env
  | Const _ -> unify Int_type t; env
  | Bool _ -> unify Bool_type t; env
  | Unit -> unify Unit_type t; env
  | Ident (name, _) -> 
    let new_type = generalize t level
    in Env.add_type env name new_type
  | Tuple (l, _) ->
    let new_types = List.map (fun _ -> new_var level) l
    in let _ = unify (Tuple_type new_types) t
    in let rec aux l l_types env =
      match (l, l_types) with 
      | [], [] -> env
      | x::l, x_type::l' -> aux l l' @@ type_pattern_matching x x_type level env
    in aux l new_types env

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



let analyse expr env = 
  let  rec inference expr env level =
    match expr with
    | Const _ -> env, Int_type
    | Bool _ -> env, Bool_type
    | Unit -> env, Unit_type
    | Ident(name, error_infos) ->
      begin
        try
          env, instanciate (Env.get_type env name) level
        with Not_found ->
          raise (send_inference_error error_infos ("identifier '" ^ name ^ "' not found"))
      end

    | Tuple (l, _) ->
      env, Tuple_type (List.map (fun x -> snd (inference x env level)) l)

    | Let(pattern, expr, _) ->
      let type_expr = snd @@ inference expr env (level + 1)
      in type_pattern_matching pattern type_expr level env, type_expr

    | LetRec(Ident(name, _), expr, _) ->
      let env' = Env.add_type env name (new_var level)
      in let type_expr = snd @@ inference expr env' (level + 1)
      in let _ = unify type_expr (Env.get_type env' name)
      in let env'' = Env.add_type env' name (generalize (Env.get_type env' name) level)
      in env'', type_expr

    | In(Let(pattern, expr, _), next, _) ->
      let type_expr = snd @@ inference expr env (level + 1)
      in inference next (type_pattern_matching pattern type_expr level env) level

    | In(LetRec(Ident(name, _), expr, _), next, _) ->
      let env' = Env.add_type env name (new_var level)
      in let type_expr = snd @@ inference expr env' (level + 1)
      in let _ = unify type_expr (Env.get_type env' name)
      in let env'' = Env.add_type env' name (generalize (Env.get_type env' name) level)
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

    | SpecComparer x -> env, x

    | Fun(args, expr, error_infos) ->
      let args_type = new_var level
      in let env' = type_pattern_matching args args_type level env
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
        | _ -> raise (send_inference_error error_infos (Printf.sprintf "Calling function with too much arguments"))
      end

    | BinOp(x, a, b, t) ->
      let _, b_type = inference b env level
      in let _, a_type = inference a env level
      in let comp_type = instanciate (x#type_check ()) level
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


in inference expr env 0

