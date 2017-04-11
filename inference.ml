open Expr
open Env
open Errors
open Lexing


(* print a type *)
let rec print_type t = 
  let tbl = Hashtbl.create 1 in
  let rec aux t = 
    match t with
    | Int_type -> "int"
    | Bool_type -> "bool"
    | Array_type -> "array int"
    | Ref_type x -> Printf.sprintf "ref %s" (aux x)
    | Unit_type -> "unit"
    | Var_type x -> begin
        match (!x) with
        | No_type y ->                      (* a bit long, because we are trying to mimic the formating of caml *)
          if not (Hashtbl.mem tbl y) then 
            Hashtbl.add tbl y (Hashtbl.length tbl); 
          let id = Hashtbl.find tbl y
          in let c = (Char.chr (Char.code 'a' + id mod 26)) 
          in if id > 26 then
            Printf.sprintf "'%c%d" c (id / 26)
          else 
            Printf.sprintf "'%c" c 
        | _ -> Printf.sprintf "Var(%s)" (aux !x)
      end
    | Fun_type (a, b) ->  begin
        match a with 
        | Fun_type _ -> Printf.sprintf ("(%s) -> %s") (aux a) (aux b) 
        | _ -> Printf.sprintf ("%s -> %s") (aux a) (aux b)
      end 

    | _ -> ""

  in aux t

(* pruning: when a Var_type is affected to a type, we must remove the Var_type to keep only the type *)
let rec prune t  = 
  match t with
  | Ref_type x -> Ref_type (prune x)
  | Fun_type (a, b) -> Fun_type (prune a, prune b)
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


(* type analysis. Lot's of code, because we are also checking for errors here*)
let rec analyse_aux node env =
  let env, out = begin
    match node with
    | Unit -> env, Unit_type
    | Bool _ -> env, Bool_type
                (* a underscore can have any value *)
    | Underscore -> env, Var_type (get_new_pol_type ())
    | Const _ -> env, Int_type 
    | Ident (x, error_infos) ->  begin
        try
          env, Env.get_type env x
        with _ ->
          raise (send_inference_error error_infos ("identifier '" ^ x ^ "' not found"))
      end

    | Not (x, t) -> begin
        try
          analyse_aux (Call(SpecComparer(Fun_type(Bool_type, Bool_type)), x, t)) env
        with InferenceError SpecComparerError ->
          let _, ta = analyse_aux x env
          in 
          raise (send_inference_error t ("Not function except an argument of type bool, not type " ^ (print_type ta  ^ "\n in expression: " ^ pretty_print_not x "" true true)))
      end

    | SpecComparer x -> env, x

    | BinOp (x, a, b, t) ->
      let _, b_type = analyse_aux b env 
      in let _, a_type = analyse_aux a env 
      in let comp_type = x#type_check ()
      in begin
        try
          analyse_aux (Call (Call(SpecComparer(comp_type), a, t), b, t)) env  
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
      let _, fun_type = analyse_aux what env 
      in let _, arg_type = analyse_aux arg env 
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


    | Fun (Unit, expr, _) ->
      let  arg_type = Unit_type
      in env, Fun_type (arg_type, snd @@ analyse_aux expr env)
    | Fun (Underscore, expr, _) ->
      let  arg_type = Var_type (get_new_pol_type ())
      in env, Fun_type (arg_type, snd @@ analyse_aux expr env)
    | Fun (Ident(x, _), expr, _) ->
      let  arg_type = Var_type (get_new_pol_type ())
      in let env' = Env.add_type env x arg_type
      in env, Fun_type (arg_type, snd @@ analyse_aux expr env')
    | Fun (_, _, error_infos) ->
      raise (send_inference_error error_infos "A fun argument must be an identifier or a unit type")

    | Let(Ident(name, _), what, _ ) -> 
      let _, def_type = analyse_aux what env 
      in Env.add_type env name def_type, def_type
    | Let(Underscore, what, _ ) -> 
      let _, def_type = analyse_aux what env 
      in env, def_type
    | LetRec(Ident(name, _), what, _ ) -> 
      let newtype = Var_type (get_new_pol_type ()) in
      let env' = Env.add_type env name newtype in
      let _, def_type = analyse_aux what env' in
      env', unify def_type newtype
    | LetRec(Underscore, what, _ ) -> 
      let newtype = Var_type (get_new_pol_type ()) in
      let _, def_type = analyse_aux what env in
      env, unify def_type newtype
    | LetRec(_, _, error_infos) | Let (_, _, error_infos) ->
      raise (send_inference_error error_infos "When declaring something with let, the left mumber must be an identifier or an underscore")

    | In(_, Let _, error_infos) | In(_, LetRec _, error_infos) ->
      raise (send_inference_error error_infos "a in statement must finish with an expression. Ending it with a let isn't authorized")

    | In (a, b, _) ->
      let nenva, _ = analyse_aux a env 
      in let nenv, t = analyse_aux b nenva   
      in begin match (a) with
        | Let(Ident(x, _), _, _) -> env, t
        | LetRec(Ident(x, _), _, _) -> env, t
        | _ -> nenv, t
      end 

     | Seq (a, b, _) | MainSeq (a, b, _) ->
      let nenva, _ = analyse_aux a env
      in analyse_aux b nenva
    | IfThenElse(cond, a, b, error_infos) ->
      let _, t = analyse_aux cond env 
      in begin match t with
        | Bool_type -> 
          let _, ta = analyse_aux a env
          in let _, tb = analyse_aux b env
          in begin
            try
              env, unify ta tb
            with InferenceError UnificationError ->
              raise (send_inference_error error_infos (Printf.sprintf "In an ifthenelse clause, the two statements must be of the same type. \n    Here if statement is of type : %s\n    And else statement is of type: %s" (print_type ta) (print_type tb)))

          end
        | _ -> raise (send_inference_error error_infos (Printf.sprintf "The condition of an ifthenelse clause must be of type bool\n  In expression %s" (Format.underline @@ pretty_print_aux cond "  " true)))
      end

    | Ref (x, _) ->
      env, Ref_type (snd @@ analyse_aux x env)

    | Bang (x, error_infos) ->
      let new_type = Var_type (get_new_pol_type ())
      in let _, t = analyse_aux x env
      in let _ = begin try
             unify (Ref_type(new_type)) t
           with InferenceError UnificationError ->
             raise (send_inference_error error_infos (Printf.sprintf "We can only dereference ref values, here we try to deference a %s.\n In expression: %s" (print_type t) (pretty_print_bang x "  " true true)))

         end
      in env , new_type

    | ArrayMake (expr, t) -> begin
        let _, arg_type = analyse_aux expr env 
        in try
          analyse_aux (Call(SpecComparer(Fun_type(Int_type, Array_type)), expr, t)) env
        with InferenceError SpecComparerError ->
          raise (send_inference_error t (Printf.sprintf "aMake constructor requires a int argument, not a %s.\n  In expression: %s" (print_type arg_type) (pretty_print_amake expr "  " true true)))
      end
    
    | Printin (expr, t) -> begin
        let _, arg_type = analyse_aux expr env 
        in try
          analyse_aux (Call(SpecComparer(Fun_type(Int_type, Int_type)), expr, t)) env
        with InferenceError SpecComparerError ->
          raise (send_inference_error t (Printf.sprintf "prInt constructor requires a int argument, not a %s.\n  In expression: %s" (print_type arg_type) (pretty_print_prInt expr "  " true true)))
      end

    | ArraySet (id, expr, nvalue, error_infos) ->
      let _, _ = analyse_aux (ArrayItem(id, expr, error_infos)) env
      in let _, tvalue = analyse_aux nvalue env
      in let _ = begin try 
             unify Int_type tvalue 
           with InferenceError (UnificationError) ->
             raise (send_inference_error error_infos (Printf.sprintf "Can't affect an expression of type %s to an element of a int Array.\n  In expression: %s" (print_type tvalue) (pretty_print_arrayset node "" true true)))
         end 
      in env, Unit_type

    | ArrayItem (id, expr, error_infos) ->
      let _ = begin try 
          unify Array_type (snd @@ analyse_aux id env)
        with InferenceError UnificationError ->
          raise (send_inference_error error_infos (Printf.sprintf "expression %s is not representing an array" (pretty_print_arrayitem node "" true true false)))
      end 
      in let _ =  begin try 
             unify Int_type (snd @@ analyse_aux expr env)
           with InferenceError UnificationError ->
             raise (send_inference_error error_infos (Printf.sprintf "Can't suscribe to the array. The index isn't an int.\n  In expression: %s" (pretty_print_arrayitem node "" true false true)))
         end in
      env, Int_type

    | Raise (e, error_infos) ->
      let _, t = analyse_aux e env
      in begin match t with
        | Int_type -> env, Var_type (get_new_pol_type ())
        | _ -> raise (InferenceError (Msg "raise"))
      end

    | TryWith (try_exp, error, with_exp, error_infos) ->
      let _, ta = analyse_aux try_exp env
      in let env = match error with
          | Const _ -> env
          | Ident(x, _) -> Env.add_type env x Int_type
          | _ ->  raise (send_inference_error error_infos "A try with instruction must match either a int or an identifier")
      in let _, tb = analyse_aux with_exp env
      in let t = begin try
             unify ta tb
           with InferenceError UnificationError ->
             raise (send_inference_error error_infos (Printf.sprintf "The two expression in a trywith clause must have the same type. Here: \n  First expression has type %s\n  Second expression has type %s" (print_type ta) (print_type tb)))
         end 
      in env, t

    | _ -> failwith "not implemented"
  end in env, prune out 

let analyse a b = analyse_aux a b
