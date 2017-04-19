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
  | _, Tuple_type l -> List.exists (fun x -> occurs_in v (prune x)) l
  | _, Var_type x -> occurs_in v (prune !x )
  | _, Fun_type (a, b) -> occurs_in v (prune a ) || occurs_in v (prune b )
  | _ -> false

(* are we in a false (or simulated) function call which as the only goal of checking if a function as a certain type ? *)
let rec is_spec_comp_call expr =
  match expr with
  | SpecComparer _ -> true
  | Call (x, _, _) -> is_spec_comp_call x
  | _ -> false

(* unify two types. It is during this step that polymorhics types are specialized *)
let rec unify t1 t2 =
  let t1 = prune t1 
  in let t2 = prune t2 in
  match (t1, t2) with
  | Ref_type x, Ref_type y -> Ref_type (unify x y)
  | Int_type, Int_type -> Int_type
  | Bool_type, Bool_type -> Bool_type
  | Array_type, Array_type -> Array_type
  | Unit_type, Unit_type -> Unit_type
  | Fun_type _, Var_type _-> unify t2 t1
  | Tuple_type l1, Tuple_type l2 when List.length l1 = List.length l2-> 
      Tuple_type (List.map (fun (x, y) -> unify x y) (List.combine l1 l2))

  | Var_type ({contents = (No_type a)} as x), Var_type ({contents = (No_type b)} as y) ->
    x := !y;
    Var_type x
  | Var_type x, _ -> if occurs_in t1 t2 then raise (InferenceError (Msg "rec")) else begin x := t2; prune t1 end
  | _, Var_type x -> if occurs_in t2 t1 then raise (InferenceError (Msg "rec")) else begin x := t1; prune t2 end
  | Fun_type (a, b), Fun_type (a', b') ->
    let a'' = unify a a'
    in let b'' = unify b b'
    in Fun_type (a'', b'')
  | _ -> raise (InferenceError (UnificationError))

let copy_type a =
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
       | _ -> t
  in aux a

(* type analysis. Lot's of code, because we are also checking for errors here*)
let rec analyse_aux is_affectation node env =
  let env, out = begin
    match node with
    | Unit -> env, Unit_type
    | Bool _ -> env, Bool_type
                (* a underscore can have any value *)
    | Underscore -> env, Var_type (get_new_pol_type ())
    | Const _ -> env, Int_type 
    | Tuple (l, _) -> (*env, Tuple_type (List.map (fun x -> snd @@ analyse_aux is_affectation x env) l)*)
      let rec aux_tuple env l = match l with
        | [] -> env, []
        | x :: t -> let env', x' = analyse_aux is_affectation x env
          in let env'', t' = aux_tuple env' t
          in env'', x'::t'
      in let env, l = aux_tuple env l
      in env, Tuple_type l
    | Ident (x, error_infos)  when not is_affectation ->  begin
        try
          env, Env.get_type env x
        with _ ->
          raise (send_inference_error error_infos ("identifier '" ^ x ^ "' not found"))
      end
    | Ident (x, error_infos) when is_affectation ->
      let env = Env.add_type env x (Var_type (get_new_pol_type()))
      in env, Env.get_type env x

    | Not (x, t) -> begin
        try
          analyse_aux is_affectation (Call(SpecComparer(Fun_type(Bool_type, Bool_type)), x, t)) env
        with InferenceError SpecComparerError ->
          let _, ta = analyse_aux is_affectation x env
          in 
          raise (send_inference_error t ("Not function except an argument of type bool, not type " ^ (print_type ta  ^ "\n in expression: " ^ pretty_print_not x "" true true)))
      end

    | SpecComparer x -> env, x

    | BinOp (x, a, b, t) ->
      let _, b_type = analyse_aux is_affectation b env 
      in let _, a_type = analyse_aux is_affectation a env 
      in let comp_type = x#type_check ()
      in begin
        try
          analyse_aux is_affectation (Call (Call(SpecComparer(comp_type), a, t), b, t)) env  
        with InferenceError (SpecComparerError) ->
          begin
            match comp_type with
            | Fun_type(a_th_type, Fun_type(b_th_type, _)) -> 
              let _ = try
                  unify a_th_type a_type
                with InferenceError UnificationError ->
                  let msg = Printf.sprintf "Operator %s, left argument: can't match type %s with type %s\n    in expression: %s" (x#symbol) (print_type b_th_type) (print_type b_type) (print_binop node "                 " true false)
                  in raise (send_inference_error t msg)
              in let _ = try
                     unify b_th_type b_type
                   with InferenceError UnificationError ->
                     let msg = Printf.sprintf "Operator %s, right argument: can't match type %s with type %s\n    in expression: %s" (x#symbol) (print_type b_th_type) (print_type b_type) (print_binop node "                 " false true)
                     in raise (send_inference_error t msg)
              in raise (InferenceError (Msg ("a boolean operator was coded in wrong format")))

            | _ -> raise (InferenceError (Msg ("a boolean operator was coded in wrong format")))
          end
      end

    | Call(what, arg, error_infos) -> 
      let _, fun_type = match what with
        | Ident (x, _) ->
          let e, t = analyse_aux is_affectation what env
          in e, copy_type t
        | _ -> analyse_aux is_affectation what env 
      in let _, arg_type = analyse_aux is_affectation arg env 
      in let storage = get_new_pol_type ()
      in begin match fun_type with
        | Var_type ({contents = No_type _}) ->
          let _ = unify (Fun_type (arg_type, (Var_type (storage)))) (fun_type) (*can't have error here, we are trying to unify a 'a with something*)
          in env, prune (Var_type storage) 
        | Fun_type (th_type, _) -> begin
            try 
              let _ = unify (Fun_type (arg_type, (Var_type (storage)))) (fun_type)
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
      let env', arg_type = analyse_aux true id env
      in env, Fun_type (arg_type, snd @@ analyse_aux is_affectation expr env')
    | Fun (Unit, expr, _) ->
      let  arg_type = Unit_type
      in env, Fun_type (arg_type, snd @@ analyse_aux is_affectation expr env)
    | Fun (Underscore, expr, _) ->
      let  arg_type = Var_type (get_new_pol_type ())
      in env, Fun_type (arg_type, snd @@ analyse_aux is_affectation expr env)
    | Fun (Ident(x, _), expr, _) ->
      let  arg_type = Var_type (get_new_pol_type ())
      in let env' = Env.add_type env x arg_type
      in env, Fun_type (arg_type, snd @@ analyse_aux is_affectation expr env')
    | Fun (_, _, error_infos) ->
      raise (send_inference_error error_infos "A fun argument must be an identifier or a unit type")

    | Let (ident, what, error_infos) ->
      let env', ident_type = analyse_aux true ident env
      in let _, def_type = analyse_aux is_affectation what env
      in begin
        try
          env', unify ident_type def_type
        with InferenceError UnificationError ->
          raise (send_inference_error error_infos (Printf.sprintf "Can't unify type %s with type %s\n  In expression: %s = ..." (print_type def_type) (print_type ident_type) (Format.underline @@ pretty_print_aux ident "  " true))) 
      end

    | LetRec(Ident(name, _), what, _ ) -> 
      let newtype = Var_type (get_new_pol_type ()) in
      let env' = Env.add_type env name newtype in
      let _, def_type = analyse_aux is_affectation what env' in
      env', unify def_type newtype


    | LetRec(_, what, error_infos ) -> 
      raise (send_inference_error error_infos "Let rec only accepts an identifier on their left side")

    | In(_, Let _, error_infos) | In(_, LetRec _, error_infos) ->
      raise (send_inference_error error_infos "a in statement must finish with an expression. Ending it with a let isn't authorized")

    | In (a, b, _) ->
      let nenva, _ = analyse_aux is_affectation a env 
      in let nenv, t = analyse_aux is_affectation b nenva   
      in begin match (a) with
        | Let(_, _, _) -> env, t
        | LetRec(_, _, _) -> env, t
        | _ -> nenv, t
      end 

     | Seq (a, b, _) | MainSeq (a, b, _) ->
      let nenva, _ = analyse_aux is_affectation a env
      in analyse_aux is_affectation b nenva
    | IfThenElse(cond, a, b, error_infos) ->
      let _, t = analyse_aux is_affectation cond env 
      in begin match t with
        | Bool_type -> 
          let _, ta = analyse_aux is_affectation a env
          in let _, tb = analyse_aux is_affectation b env
          in begin
            try
              env, unify ta tb
            with InferenceError UnificationError ->
              raise (send_inference_error error_infos (Printf.sprintf "In an ifthenelse clause, the two statements must be of the same type. \n    Here if statement is of type : %s\n    And else statement is of type: %s" (print_type ta) (print_type tb)))

          end
        | _ -> raise (send_inference_error error_infos (Printf.sprintf "The condition of an ifthenelse clause must be of type bool\n  In expression %s" (Format.underline @@ pretty_print_aux cond "  " true)))
      end

    | Ref (x, _) ->
      env, Ref_type (snd @@ analyse_aux is_affectation x env)

    | Bang (x, error_infos) ->
      let new_type = Var_type (get_new_pol_type ())
      in let _, t = analyse_aux is_affectation x env
      in let _ = begin try
             unify (Ref_type(new_type)) t
           with InferenceError UnificationError ->
             raise (send_inference_error error_infos (Printf.sprintf "We can only dereference ref values, here we try to deference a %s.\n In expression: %s" (print_type t) (pretty_print_bang x "  " true true)))

         end
      in env , new_type

    | ArrayMake (expr, t) -> begin
        let _, arg_type = analyse_aux is_affectation expr env 
        in try
          analyse_aux is_affectation (Call(SpecComparer(Fun_type(Int_type, Array_type)), expr, t)) env
        with InferenceError SpecComparerError ->
          raise (send_inference_error t (Printf.sprintf "aMake constructor requires a int argument, not a %s.\n  In expression: %s" (print_type arg_type) (pretty_print_amake expr "  " true true)))
      end
    
    | Printin (expr, t) -> begin
        let _, arg_type = analyse_aux is_affectation expr env 
        in try
          analyse_aux is_affectation (Call(SpecComparer(Fun_type(Int_type, Int_type)), expr, t)) env
        with InferenceError SpecComparerError ->
          raise (send_inference_error t (Printf.sprintf "prInt constructor requires a int argument, not a %s.\n  In expression: %s" (print_type arg_type) (pretty_print_prInt expr "  " true true)))
      end

    | ArraySet (id, expr, nvalue, error_infos) ->
      let _, _ = analyse_aux is_affectation (ArrayItem(id, expr, error_infos)) env
      in let _, tvalue = analyse_aux is_affectation nvalue env
      in let _ = begin try 
             unify Int_type tvalue 
           with InferenceError (UnificationError) ->
             raise (send_inference_error error_infos (Printf.sprintf "Can't affect an expression of type %s to an element of a int Array.\n  In expression: %s" (print_type tvalue) (pretty_print_arrayset node "" true true)))
         end 
      in env, Unit_type

    | ArrayItem (id, expr, error_infos) ->
      let _ = begin try 
          unify Array_type (snd @@ analyse_aux is_affectation id env)
        with InferenceError UnificationError ->
          raise (send_inference_error error_infos (Printf.sprintf "expression %s is not representing an array" (pretty_print_arrayitem node "" true true false)))
      end 
      in let _ =  begin try 
             unify Int_type (snd @@ analyse_aux is_affectation expr env)
           with InferenceError UnificationError ->
             raise (send_inference_error error_infos (Printf.sprintf "Can't suscribe to the array. The index isn't an int.\n  In expression: %s" (pretty_print_arrayitem node "" true false true)))
         end in
      env, Int_type

    | Raise (e, error_infos) ->
      let _, t = analyse_aux is_affectation e env
      in begin match t with
        | Int_type -> env, Var_type (get_new_pol_type ())
        | _ -> raise (InferenceError (Msg "raise"))
      end

    | TryWith (try_exp, error, with_exp, error_infos) ->
      let _, ta = analyse_aux is_affectation try_exp env
      in let env = match error with
          | Const _ -> env
          | Ident(x, _) -> Env.add_type env x Int_type
          | _ ->  raise (send_inference_error error_infos "A try with instruction must match either a int or an identifier")
      in let _, tb = analyse_aux is_affectation with_exp env
      in let t = begin try
             unify ta tb
           with InferenceError UnificationError ->
             raise (send_inference_error error_infos (Printf.sprintf "The two expression in a trywith clause must have the same type. Here: \n  First expression has type %s\n  Second expression has type %s" (print_type ta) (print_type tb)))
         end 
      in env, t

    | _ -> failwith "not implemented"
  end in env, prune out 

let analyse a b = analyse_aux false a b
