open Expr
open Env
open Errors
open Lexing


type inferrorinfo = 
  | Msg of string
  | Unification of  type_listing * type_listing
exception InferenceError of inferrorinfo
let send_inference_error infos token = 
  InferenceError (Msg (colorate red "[Inference Error]" ^ Printf.sprintf " line %d, character %d : %s" infos.pos_lnum (1 + infos.pos_cnum - infos.pos_bol) token))


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
        | No_type y -> 
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

let rec prune t d = 
  if d then Printf.printf "prune %s\n" (print_type t) else ();
  match t with
  | Ref_type x -> Ref_type (prune x d)
  | Fun_type (a, b) -> Fun_type (prune a d, prune b d)
  | Var_type x -> begin
      match (!x) with 
      | No_type _ -> t
      | _ -> x := prune !x d; !x
    end
  | _ ->  t 

let rec occurs_in v t = 
  let t = prune t false in
  match v, t with
  | _, Ref_type y -> occurs_in v y
  | Int_type, Int_type -> true
  | Bool_type, Bool_type -> true
  | Array_type, Array_type -> true
  | Unit_type, Unit_type -> true
  | _, Var_type x -> occurs_in v (prune !x false)
  | _, Fun_type (a, b) -> occurs_in v (prune a false) || occurs_in v (prune b false)
  | _ -> false

let rec unify t1 t2 =
  (*let _ =  Printf.printf "unify %s with %s \n" (print_type t1) (print_type t2 ) in*)
  let t1 = prune t1 false
  in let t2 = prune t2 false in
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
  | Var_type x, _ -> if occurs_in t1 t2 then raise (InferenceError (Msg "rec")) else begin x := t2; prune t1 false end
  | _, Var_type x -> if occurs_in t2 t1 then raise (InferenceError (Msg "rec")) else begin x := t1; prune t2 false end
  | Fun_type (a, b), Fun_type (a', b') ->
    let a'' = unify a a'
    in let b'' = unify b b'
    in Fun_type (a'', b'')
  | _ -> raise (InferenceError (Unification(t1, t2)))
  | _, _ -> raise (InferenceError (Msg (Printf.sprintf "bug %s %s\n" (print_type t1) (print_type t2))))



let rec analyse_aux unif_catch_latter node env =
  (* Printf.printf "node-> %s\n" (beautyfullprint node);*)
  let env, out = begin
    match node with
    | Unit -> env, Unit_type
    | Bool _ -> env, Bool_type
    | Const _ -> env, Int_type
    | Ident (x, error_infos) ->  begin
      try
        env, Env.get_type env x
      with _ ->
        raise (send_inference_error error_infos ("identifier '" ^ x ^ "' not found"))
      end

    | Not (x, t) -> begin
      try
          analyse_aux true (Call(SpecComparer(Fun_type(Bool_type, Bool_type)), x, t)) env
      with _ ->
        let _, ta = analyse_aux false x env
        in 
        raise (send_inference_error t ("Not function except an argument of type bool, not type " ^ (print_type ta  ^ "\n in expression: " ^ pretty_print_not node "" true true)))
          end

    | SpecComparer x -> env, x
    | BinOp (x, a, b, t) ->
      let _, b_type = analyse_aux true b env 
      in let _, a_type = analyse_aux true a env 
      in let comp_type = x#type_check ()
      in begin
        try
          analyse_aux true (Call (Call(SpecComparer(comp_type), a, t), b, t)) env  
        with InferenceError (_) ->
          begin
            let Fun_type(a_th_type, Fun_type(b_th_type, _)) = comp_type 
            in let _ = try
                   unify a_th_type a_type
                 with _ ->
                   let msg = Printf.sprintf "Operator %s, left argument: can't match type %s with type %s" (x#symbol) (print_type a_th_type) (print_type a_type)
                   in raise (send_inference_error t msg)
            in let _ = try
                   unify b_th_type b_type
                 with _ ->
                   let msg = Printf.sprintf "Operator %s, right argument: can't match type %s with type %s\n    in expression: %s" (x#symbol) (print_type b_th_type) (print_type b_type) (print_binop node "                 " false true)
                   in raise (send_inference_error t msg)
            in let _ = print_endline @@ print_type comp_type
            in raise (InferenceError (Msg "oupsi"))
          end
      end

    (*let _, a_type = analyse_aux a env 
      in let _, b_type= analyse_aux b env 
      in env, x#type_check (unify a_type b_type *)
    | Call(what, arg, error_infos) -> 
      let _, fun_type = analyse_aux false what env 
      in let _, arg_type = analyse_aux false arg env 
      in let storage = get_new_pol_type ()
      in begin match fun_type with
        | Var_type ({contents = No_type _}) ->
          let res = unify (Fun_type (arg_type, (Var_type (storage)))) (fun_type)
          in env, prune (Var_type storage) false
        | Fun_type (th_type, _) -> begin
            try 
              let res = unify (Fun_type (arg_type, (Var_type (storage)))) (fun_type)
              in env, prune (Var_type storage) false
            with _ ->
              raise (send_inference_error error_infos (Printf.sprintf "expecting this argument to be of type %s but is of type %s\n  In expression: %s" (print_type th_type) (print_type arg_type) (underline @@ pretty_print_aux arg "  " true)))
          end
        | _ -> let _ = print_endline "too much" in raise (send_inference_error error_infos "calling function with too much argument")
      end
    | Fun (Unit, expr, _) ->
      let  arg_type = Unit_type
      in env, Fun_type (arg_type, snd @@ analyse_aux false expr env)
    | Fun (Ident(x, _), expr, _) ->
      let  arg_type = Var_type (get_new_pol_type ())
      in let env' = Env.add_type env x arg_type
      in env, Fun_type (arg_type, snd @@ analyse_aux false expr env')
    | Fun (_, _, error_infos) ->
      raise (send_inference_error error_infos "A fun argument must be an identifier or a unit type")
    | Let(Ident(name, _), what, _ ) -> 
      let _, def_type = analyse_aux false what env 
      in Env.add_type env name def_type, def_type
    | Let(Underscore, what, _ ) -> 
      let _, def_type = analyse_aux false what env 
      in env, def_type
    | LetRec(Ident(name, _), what, _ ) -> 
      let newtype = Var_type (get_new_pol_type ()) in
      let env' = Env.add_type env name newtype in
      let _, def_type = analyse_aux false what env' in
      env', unify def_type newtype
    | LetRec(Underscore, what, _ ) -> 
      let newtype = Var_type (get_new_pol_type ()) in
      let _, def_type = analyse_aux false what env in
      env, unify def_type newtype
    | LetRec(_, _, error_infos) | Let (_, _, error_infos) ->
      raise (send_inference_error error_infos "When declaring something with let, the left mumber must be an identifier or an underscore")

    | In (a, b, _) ->
      let nenva, _ = analyse_aux false a env 
      in let nenv, t = analyse_aux false b nenva   
      in begin match (a) with
        | Let(Ident(x, _), _, _) -> env, t
        | LetRec(Ident(x, _), _, _) -> env, t
        | _ -> nenv, t
      end 
    | Seq (a, b, _) ->
      let nenva, _ = analyse_aux false a env
      in analyse_aux false b nenva
    | IfThenElse(cond, a, b, error_infos) ->
      let _, t = analyse_aux false cond env 
      in begin match t with
        | Bool_type -> 
          let _, ta = analyse_aux false a env
          in let _, tb = analyse_aux false b env
          in begin
            try
            env, unify ta tb
            with _ ->
              raise (send_inference_error error_infos (Printf.sprintf "In an ifthenelse clause, the two statements must be of the same type. \n    Here if statement is of type : %s\n    And else statement is of type: %s" (print_type ta) (print_type tb)))

          end
        | _ -> raise (send_inference_error error_infos "The condition of an ifthenelse clause must be of type bool")
      end
    | Ref (x, _) ->
      env, Ref_type (snd @@ analyse_aux false x env)

    | Bang (x,_) ->
      let new_type = Var_type (get_new_pol_type ())
      in let _, t = analyse_aux false x env
      in let _ = unify (Ref_type(new_type)) t
      in env , new_type

    | ArrayMake (expr, t) ->
      analyse_aux true (Call(SpecComparer(Fun_type(Int_type, Array_type)), expr, t)) env
    | Printin (expr, t) ->
      analyse_aux true (Call(SpecComparer(Fun_type(Int_type, Int_type)), expr, t)) env
          (*
          begin 
          try 
              unify Int_type (snd @@ analyse_aux expr env)
          with InferenceError x ->
              raise (InferenceError "an array must have an int argument")
          end ;
       env, Array_type *)
    | ArraySet (id, expr, nvalue, t) ->
      analyse_aux true (Call(Call(Call(SpecComparer(Fun_type(Array_type, Fun_type(Int_type, Fun_type(Int_type, Unit_type)))), id, t), expr, t), nvalue, t)) env
    | ArrayItem (id, expr, t) ->
      analyse_aux true (Call(Call(SpecComparer(Fun_type(Array_type, Fun_type(Int_type, Int_type))), id, t), expr, t)) env
          (*
              let _ = try 
              unify Array_type (snd @@ analyse_aux id env)
          with InferenceError x ->
              raise (InferenceError "an array must have an int argument")
              in let _ = 
          try 
              unify Int_type (snd @@ analyse_aux expr env)
          with InferenceError x ->
              raise (InferenceError "an array must have an int argument")
              in
       env, Int_type
*)
    | Raise (e, error_infos) ->
      let _, t = analyse_aux false e env
      in begin match t with
        | Int_type -> env, Var_type (get_new_pol_type ())
        | _ -> raise (InferenceError (Msg "raise"))
      end
    | TryWith (t_exp, Const(er), w_exp, error_infos) ->
      let _, ta = analyse_aux false t_exp env
      in let _, tb = analyse_aux false w_exp env
      in env, unify ta tb
    | TryWith (t_exp, Ident(x, _), w_exp, error_infos) ->
      let _, ta = analyse_aux false t_exp env
      in let _, tb = analyse_aux false w_exp (Env.add_type env x Int_type)
      in env, unify ta tb


    | _ -> failwith "not implemented"
  end in env, prune out false






let analyse a b = analyse_aux false a b
