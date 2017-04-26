open Prettyprint
open Expr
open Env
open Errors
open Lexing



(* pruning: when a Var_type is affected to a type, we must remove the Var_type to keep only the type *)
let rec prune t  = 
  match t with
  | Ref_type x -> Ref_type (prune x)
  | Fun_type (a, b) -> Fun_type (prune a, prune b)
  | Tuple_type l -> Tuple_type (List.map (fun x -> prune x) l)
  | Params_type l -> Params_type (List.map (fun x -> prune x) l)
  | Called_type (name, t) -> Called_type(name, prune t)
  | Constructor_type (n, a, b) -> Constructor_type (n, prune a, prune b)
  | Constructor_type_noarg (n, a) -> Constructor_type_noarg (n, prune a)
  | Arg_type x -> prune x
  | Var_type x -> begin
      match (!x) with 
      | No_type _ -> t
      | _ -> x := prune !x; !x
    end
  | _ ->  t 
(* check if a base term occurs in another one *)
let rec occurs_in v t = 
  let t = prune t in
  match v, t with
  | _, Ref_type y -> occurs_in v y
  | Int_type, Int_type -> true
  | Bool_type, Bool_type -> true
  | Array_type, Array_type -> true
  | Unit_type, Unit_type -> true
  | Var_type({contents = No_type a}), Var_type({contents = No_type b}) when a = b -> true
  | _, Tuple_type l -> List.exists (fun x -> occurs_in v (prune x)) l
  | _, Params_type l -> List.exists (fun x -> occurs_in v (prune x)) l
  | _, Var_type x -> occurs_in v (prune !x )
  | _, Fun_type (a, b) -> occurs_in v (prune a ) || occurs_in v (prune b )
  | _, Called_type (_, t) -> occurs_in v t
  | _ -> false



(* are we in a false (or simulated) function call which as the only goal of checking if a function as a certain type ? *)
let rec is_spec_comp_call expr =
  match expr with
  | SpecComparer _ -> true
  | Call (x, _, _) -> is_spec_comp_call x
  | _ -> false



(* unify two types. It is during this step that polymorhics types are specialized *)
let unify tbl t1 t2 =

 (* let _ = Printf.printf "unification of %s \n" (print_type (Params_type([t1; t2])))
      in*)
  let rec unify_aux t1 t2 =
  let t1 = prune t1 
  in let t2 = prune t2 in
 (* let _ = Printf.printf "unification inside of %s \n" (print_type (Params_type([t1; t2])))
      in*)
  match (t1, t2) with
  | Constructor_type_noarg (name, father), Constructor_type_noarg(name', father') 
    when name = name' -> 
    prune father'
  | Called_type (n, t), Called_type (n', t') when n = n' ->
    Called_type (n, unify_aux t t')
  | Constructor_type(name, father, t), Constructor_type(name', father', t') when name = name' ->
    let _ = unify_aux t' t
    in prune father'
  | Ref_type x, Ref_type y -> Ref_type (unify_aux x y)
  | Int_type, Int_type -> Int_type
  | Bool_type, Bool_type -> Bool_type
  | Array_type, Array_type -> Array_type
  | Unit_type, Unit_type -> Unit_type
  | Fun_type _, Var_type _-> unify_aux t2 t1
  | Tuple_type l1, Tuple_type l2 when List.length l1 = List.length l2-> 
    Tuple_type (List.map (fun (x, y) -> unify_aux x y) (List.combine l1 l2))
  | Params_type l1, Params_type l2 when List.length l1 = List.length l2-> 
    Params_type (List.map (fun (x, y) -> unify_aux x y) (List.combine l1 l2))

(* we order the polymorphic vars: this allow us to affect in a good ways the pointers. hen two poltypes a & b are seen, the one changed is deterministic (allows use to solve bug like with the typing of fold_left *)
  | Var_type ({contents = (No_type a)} as x), Var_type ({contents = (No_type b)} as y) -> 
    if a = b then t1 else 
      let _ = if a < b then 
          (x := !y; Hashtbl.add tbl a (prune t2) )
        else (y := !x; Hashtbl.add tbl b (prune t1)) in
      Var_type x

  | Var_type ({contents= No_type a} as x), _ -> 
    if occurs_in t1 t2 then 
      raise (InferenceError (Msg (Printf.sprintf "Unification error. Can't unify these two types: %s because one occurs in the other" (print_type (Params_type [t1; t2])))))
    else 
      begin  
        x := t2; 
        Hashtbl.add tbl a (prune t2);
        prune t1 
      end
  | _, Var_type ({contents= No_type a} as x) -> 
    if occurs_in t2 t1 then 
      raise (InferenceError (Msg (Printf.sprintf "Unification error. Can't unify these two types: %s because one occurs in the other" (print_type (Params_type [t1; t2])))))
    else 
      begin 
        x := t1; 
        Hashtbl.add tbl a (prune t1);
        prune t2 
      end
  | Var_type x, _ -> if occurs_in t1 t2 then raise (InferenceError (Msg "rec")) else begin Printf.printf "went here\n"; x := t2;  prune t1 end
  | _, Var_type x -> if occurs_in t2 t1 then raise (InferenceError (Msg "rec")) else begin Printf.printf "went here\n"; x := t1; prune t2 end
  | Fun_type (a, b), Fun_type (a', b') ->
    let a'' = unify_aux a a'
    in let b'' = unify_aux b b'
    in Fun_type (a'', b'')
  | No_type x, No_type y when x = y -> t1
  | Arg_type x, Arg_type y -> Arg_type (unify_aux x y)

  | _ -> raise (InferenceError (UnificationError))
      in let out = unify_aux t1 t2
     (* in let _ = Printf.printf ("result: %s\n") (print_type out) *)
      in out

let update_type tbl t =
(* let _ = Hashtbl.iter (fun a b -> Printf.printf ", %d:%s" a (print_type b)) tbl in
 let _ = print_endline "" in*)
  let rec aux_update t =
    match t with
    | Var_type ({contents = No_type a}) ->
      if Hashtbl.mem tbl a then (
        true, Hashtbl.find tbl a)
      else false, t
    | Var_type x -> 
      let s, r = aux_update !x 
      in let _ = x := r
      in s,  Var_type x
    | Ref_type x -> 
      let s, r = aux_update x
      in s, Ref_type r
    | Arg_type x -> 
      let s, r = aux_update x
      in s, Arg_type r
    | Fun_type (a, b) ->
      let s_a, r_a = aux_update a
      in let s_b, r_b = aux_update b
      in s_a || s_b, Fun_type (r_a, r_b)
    | Constructor_type (a, b, l) ->
      let s_b, r_b = aux_update b
      in let s_l, r_l = aux_update l
      in s_b || s_l, Constructor_type (a, r_b, r_l)
    | Constructor_type_noarg (a, b) ->
      let s, r = aux_update b 
      in s, Constructor_type_noarg(a, r)
    | Called_type (a, l) ->
      let s, r = aux_update l
      in s, Called_type(a, r)
    | Tuple_type l ->
      let l' = List.map aux_update l
      in let s, r = List.split l'
      in List.fold_left (||) (List.hd s) (List.tl s), Tuple_type r
    | Params_type l ->
      let l' = List.map aux_update l
      in let s, r = List.split l'
      in List.fold_left (||) (List.hd s) (List.tl s), Params_type r
    | _ -> false, t

    in let rec aux t =
         let s, r = aux_update t in
         if s then aux r
         else t
    in aux t

let copy_type a =
  (*let _ = Printf.printf "copy of %s\n" (print_type a) in*)
  let tbl = Hashtbl.create 0
  in let rec aux t =
       match t with
       | Var_type ({contents = No_type x}) ->
         let _ = 
           if not (Hashtbl.mem tbl x) then
             Hashtbl.add tbl x (get_new_pol_type ()) ;
         in
         Var_type ((Hashtbl.find tbl x))
       | Var_type x -> Var_type (ref (aux !x))
       | Fun_type (a, b) -> Fun_type (aux a, aux b)
       | Ref_type x -> Ref_type (aux x)
       | Tuple_type l -> Tuple_type (List.map aux l)
       | Params_type l -> Params_type (List.map aux l)
       | Constructor_type (a, b, l) -> Constructor_type (a, aux b, aux l)
       | Constructor_type_noarg (a, b) -> Constructor_type_noarg (a, aux b)
       | Called_type (a, l) -> Called_type(a, aux l)
       | Arg_type x -> Arg_type (aux x)
       | _ -> t
  in aux a


(* temp copy *)
let check_call_type_decl_valid types =
  match types with
  | Params_type l -> 
    let rec aux l =
      match l with
      | [] -> true
      | x::tl -> if List.mem x tl then false
        else aux tl
    in aux l
  | _ -> true

let rec find_new_type_decl_name name env = 
  let name = " " ^ name
  in if Env.mem_type env name then
    find_new_type_decl_name name env
  else 
    name
let rec find_last_oc name env =
  let name = " " ^ name in
  if Env.mem_type env  name then
    let t = find_last_oc name env
    in if t = "" then name else t
  else ""

let check_compatibility t1 t2 error =
  match (t1, t2) with
  | Called_type(_, No_type _), Called_type(_, No_type _) -> true
  | Called_type(name, Params_type l), Called_type(_, Params_type l') -> 
    let ll = List.length l
    in let ll' = List.length l'
    in if ll = ll' then true
    else
      raise (send_inference_error error (Printf.sprintf "not enough argument for type %s: expecting %d arguments, got %d" name ll ll'))
  | Called_type _, Called_type (name, _)-> raise (send_inference_error error (Printf.sprintf "Perhaps you have forget (or just put too much) an argument for the type %s" name))
  | _, _ -> failwith "bad arguments"

let rec update_types_name type_name new_type env error t =
  let aux = update_types_name type_name new_type env error in
  match t with
  | Tuple_type l -> Tuple_type (List.map aux l)
  | Params_type l -> Params_type (List.map aux l)
  | Constructor_type (a, b, l) -> Constructor_type (a, aux b, aux l)
  | Constructor_type_noarg(a, b) -> Constructor_type_noarg(a, aux b)
  | Ref_type x                  -> Ref_type (aux x)
  | Var_type x                  -> (x := (aux !x); t)
  | Arg_type x                  -> Arg_type (aux x)
  | Fun_type (a, b)             -> Fun_type (aux a, aux b)
  | Called_type (name, b)       ->
    let new_name = find_last_oc name env
    in if type_name = name then
      if check_compatibility new_type t error then
          if new_name = "" then
            Called_type (" " ^ name, b)
          else 
            Called_type (" " ^ new_name, b)
        else failwith "ouspi"
    else
    if new_name = "" then
        raise (send_inference_error error (Printf.sprintf "incorrect identifier %s" name))
    else if check_compatibility (Env.get_type env new_name) t error then 
      Called_type(new_name, b)
    else failwith "oupsi"
  | _ -> t

let interpret_type_declaration new_type constructor_list error env =
  match new_type with
  | Called_type(name_decl, types) ->
    if check_call_type_decl_valid types then
      let name = find_new_type_decl_name name_decl env in
      begin
        let rec aux env l =
          match l with
          | [] ->  Env.add_type env name (Called_type(name, types)), (Called_type(name, types))
          | Constructor_type_noarg(name_constr, _)::tl ->
            let nt = Constructor_type_noarg (name_constr, Called_type(name, types))
            in let env = Env.add_type env name_constr nt
            in aux env tl
          | Constructor_type(name_constr, _, expr)::tl ->
            let nt = Constructor_type (name_constr, Called_type(name, types), update_types_name name_decl new_type env error expr)
            in let env = Env.add_type env name_constr nt
            in aux env tl
          | _ -> raise (send_error "Waited for a valid constructor declaration" error)
        in aux env constructor_list
      end
    else 
      raise (send_error "You have a duplicate polymorphic type in this declaration" error)

  | _ -> raise (send_error "Waited for an expr name" error)


(* type analysis. Lot's of code, because we are also checking for errors here*)
let rec analyse_aux tbl is_argument is_affectation node env =
  let env, out = begin
    match node with
    | Unit -> env, Unit_type
    | Bool _ -> env, Bool_type
    (* a underscore can have any value *)
    | Underscore -> env, Var_type (get_new_pol_type ())
    | Const _ -> env, Int_type 
    | Constructor_noarg (name, error_infos) -> 
      if Env.mem_type env name then
        let u = copy_type @@ Env.get_type env name
        in begin
          try
            env, unify tbl (Constructor_type_noarg(name, Unit_type)) u  
          with InferenceError UnificationError ->
            begin
              match u with
              | Constructor_type (_, _, l) ->
                raise (send_inference_error error_infos "expected a constructor with arguments")
              | _ ->
                raise (send_inference_error error_infos "unexpected error")
            end
        end
      else 
        raise (send_inference_error error_infos (Printf.sprintf "Constructor %s not defined" name))
    | TypeDecl(id, l, error_infos) -> 
      interpret_type_declaration id l error_infos env
    | Tuple (l, _) -> (*env, Tuple_type (List.map (fun x -> snd @@ analyse_aux tbl is_argument is_affectation x env) l)*)
      let rec aux_tuple env l = match l with
        | [] -> env, []
        | x :: t -> let env', x' = analyse_aux tbl is_argument is_affectation x env
          in let env'', t' = aux_tuple env' t
          in env'', x'::t'
      in let env, l = aux_tuple env l
      in env, Tuple_type l
    | Ident (x, error_infos)  when not is_affectation ->  begin
        try
          env, match (prune @@ Env.get_type env x) with
          | Arg_type x -> x
          | Fun_type _ as x -> copy_type x
          | Var_type {contents = No_type _} as x -> x
        (*  | Constructor_type_noarg _ as x -> copy_type x
          | Constructor_type _ as x -> copy_type x
          | Called_type _ as x -> copy_type x
          | Params_type _ as x -> copy_type x
          | Tuple_type _ as x -> copy_type x
          | Polymorphic_type _ as x -> copy_type x
          | No_type _ as x -> copy_type x
        *)  
          
          | x -> x

        with _ ->
          raise (send_inference_error error_infos ("identifier '" ^ x ^ "' not found"))
      end
    | Ident (x, error_infos) when is_affectation ->
      let new_type = if is_argument then
            Arg_type(Var_type(get_new_pol_type()))
        else Var_type(get_new_pol_type())
            in
      let env = Env.add_type env x new_type
      in env, Env.get_type env x

    | Not (x, t) -> begin
        try
          analyse_aux tbl is_argument is_affectation (Call(SpecComparer(Fun_type(Bool_type, Bool_type)), x, t)) env
        with InferenceError SpecComparerError ->
          let _, ta = analyse_aux tbl is_argument is_affectation x env
          in 
          raise (send_inference_error t ("Not function except an argument of type bool, not type " ^ (print_type ta  ^ "\n in expression: " ^ pretty_print_not x "" true true)))
      end

    | SpecComparer x -> env, x

    | BinOp (x, a, b, t) ->
      let _, b_type = analyse_aux tbl is_argument is_affectation b env 
      in let _, a_type = analyse_aux tbl is_argument is_affectation a env 
      in let comp_type = x#type_check ()
      in begin
        try
          analyse_aux tbl is_argument is_affectation (Call (Call(SpecComparer(comp_type), a, t), b, t)) env  
        with InferenceError (SpecComparerError) ->
          begin
            match comp_type with
            | Fun_type(a_th_type, Fun_type(b_th_type, _)) -> 
              let _ = try
                  unify tbl a_th_type a_type
                with InferenceError UnificationError ->
                  let msg = Printf.sprintf "Operator %s, left argument: can't match type %s with type %s\n    in expression: %s" (x#symbol) (print_type b_th_type) (print_type b_type) (print_binop node "                 " true false)
                  in raise (send_inference_error t msg)
              in let _ = try
                     unify tbl b_th_type b_type
                   with InferenceError UnificationError ->
                     let msg = Printf.sprintf "Operator %s, right argument: can't match type %s with type %s\n    in expression: %s" (x#symbol) (print_type b_th_type) (print_type b_type) (print_binop node "                 " false true)
                     in raise (send_inference_error t msg)
              in raise (InferenceError (Msg ("a boolean operator was coded in wrong format")))

            | _ -> raise (InferenceError (Msg ("a boolean operator was coded in wrong format")))
          end
      end

    | Constructor(name, arg, error_infos) 
    | Call(Constructor_noarg (name, _), arg, error_infos) ->
      if Env.mem_type env name then
        let u = copy_type @@ Env.get_type env name
        in let env', t_arg = analyse_aux tbl is_argument is_affectation arg env
        in begin
          try
            env', unify tbl (Constructor_type(name, Unit_type, prune t_arg)) u 
          with InferenceError UnificationError ->
            begin
              match u with
              | Constructor_type_noarg _ ->
                raise (send_inference_error error_infos "expected a constructor without arguments")
              | Constructor_type (_, _, l) ->
                let l = prune l in
                raise (send_inference_error error_infos (Printf.sprintf "argument was expected to have type %s but had type %s" (print_type l) (print_type t_arg)))
              | _ -> failwith "bad type"
            end
        end
      else 
        raise (send_inference_error error_infos (Printf.sprintf "Constructor %s not defined" name))


    | Call(what, arg, error_infos) -> 
      let _, fun_type = analyse_aux tbl is_argument is_affectation what env 
      in let _, arg_type = analyse_aux tbl is_argument is_affectation arg env 
      in let storage = get_new_pol_type ()
      in begin match fun_type with
        | Var_type ({contents = No_type _}) ->
          let _ = unify tbl (fun_type) (Fun_type (arg_type, (Var_type (storage)))) (*can't have error here, we are trying to unify tbl a 'a with something*)
          in env, prune (Var_type storage) 
        | Fun_type (th_type, _) -> begin
            try 
              let _ = unify tbl fun_type (Fun_type (arg_type, (Var_type (storage)))) 
              in env, prune (Var_type storage) 
            with InferenceError UnificationError ->
              begin 
                if is_spec_comp_call what then 
                  raise (InferenceError (SpecComparerError))
                else 
                  raise (send_inference_error error_infos (Printf.sprintf "expecting this argument to be of type %s but is of type %s\n  In expression: %s" (print_type th_type) (print_type arg_type) (Format.underline @@ pretty_print_aux arg "  " true))) 
              end
          end
        | _ -> let _ = print_endline "too much" in raise (send_inference_error error_infos "calling function with too much argument")
      end


    | Fun (id, expr, _) ->
      let env', arg_type = analyse_aux tbl true true id env
      in env, Fun_type (arg_type, snd @@ analyse_aux tbl is_argument is_affectation expr env')

    | Let (ident, what, error_infos) ->
      let env', ident_type = analyse_aux tbl is_argument true ident env
      in let _, def_type = analyse_aux tbl is_argument is_affectation what env
      in begin
        try
          env', unify tbl ident_type def_type
        with InferenceError UnificationError ->
          raise (send_inference_error error_infos (Printf.sprintf "Can't unify type %s with type %s\n  In expression: %s = ..." (print_type def_type) (print_type ident_type) (Format.underline @@ pretty_print_aux ident "  " true))) 
      end

    | LetRec(Ident(name, _), what, _ ) -> 
      let newtype = Var_type (get_new_pol_type ()) in
      let env' = Env.add_type env name newtype in
      let _, def_type = analyse_aux tbl is_argument is_affectation what env' in
      env', unify tbl def_type newtype


    | LetRec(_, what, error_infos ) -> 
      raise (send_inference_error error_infos "Let rec only accepts an identifier on their left side")

    | In(_, Let _, error_infos) | In(_, LetRec _, error_infos) ->
      raise (send_inference_error error_infos "a in statement must finish with an expression. Ending it with a let isn't authorized")

    | In (a, b, _) ->
      let nenva, _ = analyse_aux tbl is_argument is_affectation a env 
      in let nenv, t = analyse_aux tbl is_argument is_affectation b nenva   
      in begin match (a) with
        | Let(_, _, _) -> env, t
        | LetRec(_, _, _) -> env, t
        | _ -> nenv, t
      end 

    | Seq (a, b, _) | MainSeq (a, b, _) ->
      let nenva, _ = analyse_aux tbl is_argument is_affectation a env
      in analyse_aux tbl is_argument is_affectation b nenva
    | IfThenElse(cond, a, b, error_infos) ->
      let _, t = analyse_aux tbl is_argument is_affectation cond env 
      in begin try
          let _  = unify tbl t Bool_type in
          let _, ta = analyse_aux tbl is_argument is_affectation a env
          in let _, tb = analyse_aux tbl is_argument is_affectation b env
          in begin
            try
              env, unify tbl ta tb
            with InferenceError UnificationError ->
              raise (send_inference_error error_infos (Printf.sprintf "In an ifthenelse clause, the two statements must be of the same type. \n    Here if statement is of type : %s\n    And else statement is of type: %s" (print_type ta) (print_type tb)))

          end
        with InferenceError UnificationError ->
        raise (send_inference_error error_infos (Printf.sprintf "The condition of an ifthenelse clause must be of type bool not %s\n  In expression %s"(print_type t) (Format.underline @@ pretty_print_aux cond "  " true)))
      end
      (*
      let _, t = analyse_aux tbl is_argument is_affectation cond env 
      in begin match t with
        | Bool_type -> 
          let _, ta = analyse_aux tbl is_argument is_affectation a env
          in let _, tb = analyse_aux tbl is_argument is_affectation b env
          in begin
            try
              env, unify tbl ta tb
            with InferenceError UnificationError ->
              raise (send_inference_error error_infos (Printf.sprintf "In an ifthenelse clause, the two statements must be of the same type. \n    Here if statement is of type : %s\n    And else statement is of type: %s" (print_type ta) (print_type tb)))

          end
        | _ -> raise (send_inference_error error_infos (Printf.sprintf "The condition of an ifthenelse clause must be of type bool\n  In expression %s" (Format.underline @@ pretty_print_aux cond "  " true)))
      end
*)
    | Ref (x, _) ->
      env, Ref_type (snd @@ analyse_aux tbl is_argument is_affectation x env)

    | Bang (x, error_infos) ->
      let new_type = Var_type (get_new_pol_type ())
      in let _, t = analyse_aux tbl is_argument is_affectation x env
      in let _ = begin try
             unify tbl (Ref_type(new_type)) t
           with InferenceError UnificationError ->
             raise (send_inference_error error_infos (Printf.sprintf "We can only dereference ref values, here we try to deference a %s.\n In expression: %s" (print_type t) (pretty_print_bang x "  " true true)))

         end
      in env , new_type

    | ArrayMake (expr, t) -> begin
        let _, arg_type = analyse_aux tbl is_argument is_affectation expr env 
        in try
          analyse_aux tbl is_argument is_affectation (Call(SpecComparer(Fun_type(Int_type, Array_type)), expr, t)) env
        with InferenceError SpecComparerError ->
          raise (send_inference_error t (Printf.sprintf "aMake constructor requires a int argument, not a %s.\n  In expression: %s" (print_type arg_type) (pretty_print_amake expr "  " true true)))
      end

    | Printin (expr, t) -> begin
        let _, arg_type = analyse_aux tbl is_argument is_affectation expr env 
        in try
          analyse_aux tbl is_argument is_affectation (Call(SpecComparer(Fun_type(Int_type, Int_type)), expr, t)) env
        with InferenceError SpecComparerError ->
          raise (send_inference_error t (Printf.sprintf "prInt constructor requires a int argument, not a %s.\n  In expression: %s" (print_type arg_type) (pretty_print_prInt expr "  " true true)))
      end

    | ArraySet (id, expr, nvalue, error_infos) ->
      let _, _ = analyse_aux tbl is_argument is_affectation (ArrayItem(id, expr, error_infos)) env
      in let _, tvalue = analyse_aux tbl is_argument is_affectation nvalue env
      in let _ = begin try 
             unify tbl Int_type tvalue 
           with InferenceError (UnificationError) ->
             raise (send_inference_error error_infos (Printf.sprintf "Can't affect an expression of type %s to an element of a int Array.\n  In expression: %s" (print_type tvalue) (pretty_print_arrayset node "" true true)))
         end 
      in env, Unit_type

    | ArrayItem (id, expr, error_infos) ->
      let _ = begin try 
          unify tbl Array_type (snd @@ analyse_aux tbl is_argument is_affectation id env)
        with InferenceError UnificationError ->
          raise (send_inference_error error_infos (Printf.sprintf "expression %s is not representing an array" (pretty_print_arrayitem node "" true true false)))
      end 
      in let _ =  begin try 
             unify tbl Int_type (snd @@ analyse_aux tbl is_argument is_affectation expr env)
           with InferenceError UnificationError ->
             raise (send_inference_error error_infos (Printf.sprintf "Can't suscribe to the array. The index isn't an int.\n  In expression: %s" (pretty_print_arrayitem node "" true false true)))
         end in
      env, Int_type

    | Raise (e, error_infos) ->
      let _, t = analyse_aux tbl is_argument is_affectation e env
      in begin match t with
        | Int_type -> env, Var_type (get_new_pol_type ())
        | _ -> raise (InferenceError (Msg "raise"))
      end

    | TryWith (try_exp, error, with_exp, error_infos) ->
      let _, ta = analyse_aux tbl is_argument is_affectation try_exp env
      in let env = match error with
          | Const _ -> env
          | Ident(x, _) -> Env.add_type env x Int_type
          | _ ->  raise (send_inference_error error_infos "A try with instruction must match either a int or an identifier")
      in let _, tb = analyse_aux tbl is_argument is_affectation with_exp env
      in let t = begin try
             unify tbl ta tb
           with InferenceError UnificationError ->
             raise (send_inference_error error_infos (Printf.sprintf "The two expression in a trywith clause must have the same type. Here: \n  First expression has type %s\n  Second expression has type %s" (print_type ta) (print_type tb)))
         end 
      in env, t
    | MatchWith (match_expr, matches, errors) ->
      let _, match_expr_type = analyse_aux tbl is_argument is_affectation match_expr env
      in let temp = List.map (fun (m, a) -> 
          let env', t = analyse_aux tbl is_argument true m env 
          in t, snd @@ analyse_aux tbl is_argument is_affectation a env')
          matches
      in let pattern_types, action_types = List.split temp
      in let _ = List.fold_left (fun a b -> begin
            try
              unify tbl a b
            with InferenceError UnificationError ->
              raise (send_inference_error errors (Printf.sprintf "can't unify %s and %s in pattern matching" (print_type a) (print_type b)))   
          end   ) match_expr_type pattern_types
      in env, List.fold_left (fun a b -> begin
            try
              unify tbl a b
            with InferenceError UnificationError ->
              raise (send_inference_error errors (Printf.sprintf "Can't unify expressions in matching. Should it return %s or %s?" (print_type a) (print_type b)))
          end )
          (List.hd action_types) (List.tl action_types)

    | _ -> failwith "not implemented"
  end in env, update_type tbl ( prune out) 

let analyse a b =
  let tbl = Hashtbl.create 50 in
 analyse_aux tbl false false a b
