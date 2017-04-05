open Expr
open Env
exception InferenceError of string

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
          Printf.sprintf "'%d" (Hashtbl.find tbl y)
        | _ -> Printf.sprintf "Var(%s)" (aux !x)
  end
  | Fun_type (a, b) -> Printf.sprintf ("%s -> (%s)") (aux a) (aux b)
  | _ -> ""

in aux t

let rec prune t d = 
  if d then Printf.printf "prune %s\n" (print_type t) else ();
  match t with
  | Var_type x -> begin
      match (!x) 
      with 
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
  let _ =  Printf.printf "unify %s with %s \n" (print_type t1) (print_type t2 ) in
  let t1 = prune t1 true
  in let t2 = prune t2 true in
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
  | Var_type x, _ -> if occurs_in t1 t2 then raise (InferenceError ("rec")) else begin x := t2; prune t1 false end
  | _, Var_type x -> if occurs_in t2 t1 then raise (InferenceError ("rec")) else begin x := t1; prune t2 false end
  | Fun_type (a, b), Fun_type (a', b') ->
    let a'' = unify a a'
    in let b'' = unify b b'
    in Fun_type (a'', b'')
  | _, _ -> raise (InferenceError (Printf.sprintf "bug %s %s\n" (print_type t1) (print_type t2)))



let rec analyse node env  =
  Printf.printf "node-> %s\n" (beautyfullprint node);
  match node with
  | Unit -> env, Unit_type
  | Bool _ -> env, Bool_type
  | Const _ -> env, Int_type
  | Ident (x, _) -> env, Env.get_most_recent env x
  | SpecComparer x -> env, x
  | BinOp (x, a, b, t) ->
    let _, b_type = analyse a env 
    in let _, a_type = analyse b env 
    in let rec tryhard l = 
         match l with
         | [] -> raise (InferenceError "no inference found for this binop")
         | x::tl -> try
             analyse (Call (Call(SpecComparer(x), a, t), b, t)) env  
           with InferenceError x ->
             tryhard tl
    in tryhard x#type_check
  (*let _, a_type = analyse a env 
    in let _, b_type= analyse b env 
    in env, x#type_check (unify a_type b_type *)
  | Call(what, arg, _ ) -> 
    let _, fun_type = analyse what env 
    in let _, arg_type = analyse arg env 
    in let _ = Printf.printf "fun %s %s\n" (print_type fun_type) (beautyfullprint what)
    in let storage = get_new_pol_type ()
    in let res = unify (Fun_type (arg_type, (Var_type (storage)))) (fun_type)
    in let _ = Printf.printf "---> %s\n" (print_type fun_type)
    in env, prune (Var_type storage) false
  | Fun (Ident(x, _), expr, _) ->
    let  arg_type = Var_type (get_new_pol_type ())
    in let env' = Env.add env x arg_type
    in env, Fun_type (arg_type, snd @@ analyse expr env')
  | Let(Ident(name, _), what, _ ) -> 
    let _, def_type = analyse what env 
    in Printf.sprintf "%s : %s" name (print_type def_type); 
    Env.add env name def_type, def_type
  | LetRec(Ident(name, _), what, _ ) -> 
    let newtype = Var_type (get_new_pol_type ()) in
    let env' = Env.add env name newtype in
    let _, def_type = analyse what env' in
    env', unify def_type newtype

  | In (a, b, _) ->
          let nenva, _ = analyse a env 
        in let nenv, t = analyse b nenva   
        in begin match (a) with
          | Let(Ident(x, _), _, _) -> env, t
          | LetRec(Ident(x, _), _, _) -> env, t
          | _ -> nenv, t
        end 
  | IfThenElse(cond, a, b, _) ->
    let _, _ = analyse cond env 
    in let _, ta = analyse a env
    in let _, tb = analyse b env
    in env, unify ta tb
  | Ref (x, _) ->
          print_string "reeeeeeeeeeeeeeeeeeeeeeeeeef\n";
    env, Ref_type (snd @@ analyse x env)

  | Bang (x,_) ->
          let new_type = Var_type (get_new_pol_type ())
          in let _, t = analyse x env
          in let _ = unify (Ref_type(new_type)) t
          in env , new_type

  | ArrayMake (expr, t) ->
          analyse (Call(SpecComparer(Fun_type(Int_type, Array_type)), expr, t)) env
  | Printin (expr, t) ->
          analyse (Call(SpecComparer(Fun_type(Int_type, Int_type)), expr, t)) env
          (*
          begin 
          try 
              unify Int_type (snd @@ analyse expr env)
          with InferenceError x ->
              raise (InferenceError "an array must have an int argument")
          end ;
       env, Array_type *)
  | ArraySet (id, expr, nvalue, t) ->
          analyse (Call(Call(Call(SpecComparer(Fun_type(Array_type, Fun_type(Int_type, Fun_type(Int_type, Unit_type)))), id, t), expr, t), nvalue, t)) env
  | ArrayItem (id, expr, t) ->
          analyse (Call(Call(SpecComparer(Fun_type(Array_type, Fun_type(Int_type, Int_type))), id, t), expr, t)) env
          (*
              let _ = try 
              unify Array_type (snd @@ analyse id env)
          with InferenceError x ->
              raise (InferenceError "an array must have an int argument")
              in let _ = 
          try 
              unify Int_type (snd @@ analyse expr env)
          with InferenceError x ->
              raise (InferenceError "an array must have an int argument")
              in
       env, Int_type
*)

  | _ -> raise (InferenceError "not implemented")





