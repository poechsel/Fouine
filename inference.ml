open Expr
open Env

let rec print_type t = match t with
  | Int_type -> "int"
  | Bool_type -> "bool"
  | Array_type -> "array"
  | Unit_type -> "unit"
  | Var_type x when !x = No_type -> "'a"
  | Var_type x -> Printf.sprintf "Var(%s)" (print_type !x)
  | Fun_type (a, b) -> Printf.sprintf ("%s -> (%s)") (print_type a) (print_type b)
  | _ -> ""

let rec prune t d = 
  if d then Printf.printf "prune %s\n" (print_type t) else ();
  match t with
  | Var_type x when !x = No_type -> t
  | Var_type x -> x := prune !x d; !x
  | _ ->  t 

let rec occurs_in v t = 
  let t = prune t false in
  match v, t with
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
    | Int_type, Int_type -> Int_type
    | Bool_type, Bool_type -> Bool_type
    | Array_type, Array_type -> Array_type
    | Unit_type, Unit_type -> Unit_type
    | Fun_type _, Var_type _-> unify t2 t1
    | Var_type x, _ -> if occurs_in t1 t2 then failwith "rec" else begin x := t2; prune t1 false end
    | _, Var_type x -> if occurs_in t2 t1 then failwith "rec" else begin x := t1; prune t2 false end
    | Fun_type (a, b), Fun_type (a', b') ->
      let a'' = unify a a'
      in let b'' = unify b b'
      in Fun_type (a'', b'')
    | _, _ -> failwith (Printf.sprintf "bug %s %s\n" (print_type t1) (print_type t2))



let rec analyse node env non_generic =
  Printf.printf "node-> %s\n" (beautyfullprint node);
  match node with
  | Unit -> env, Unit_type
  | Bool _ -> env, Bool_type
  | Const _ -> env, Int_type
  | Ident (x, _) -> env, Env.get_most_recent env x
  | Ref _ -> env, Fun_type (Int_type, Fun_type(Int_type, Int_type))
  | SpecComparer x -> env, x
  | BinOp (x, a, b, t) ->
    let _, b_type = analyse a env non_generic
    in let _, a_type = analyse b env non_generic
    in analyse (Call (Call(SpecComparer(Fun_type (Int_type, Fun_type(Int_type, Int_type))), Const 1, t), Const 1, t)) env non_generic
    (*let _, a_type = analyse a env non_generic
    in let _, b_type= analyse b env non_generic
    in env, x#type_check (unify a_type b_type *)
  | Call(what, arg, _ ) -> 
    let _, fun_type = analyse what env non_generic
    in let _, arg_type = analyse arg env non_generic
    in let _ = Printf.printf "fun %s %s\n" (print_type fun_type) (beautyfullprint what)
    in let storage = ref No_type 
    in let res = unify (Fun_type (arg_type, (Var_type (storage)))) (fun_type)
    in let _ = Printf.printf "---> %s\n" (print_type fun_type)
    in env, prune (Var_type storage) false
  | Fun (Ident(x, _), expr, _) ->
    let  arg_type = Var_type (ref No_type)
    in let env' = Env.add env x arg_type
in let ng' = (arg_type) :: non_generic
in env, Fun_type (arg_type, snd @@ analyse expr env' ng')
  | Let(Ident(name, _), what, _ ) -> 
    let _, def_type = analyse what env non_generic
    in Printf.sprintf "%s : %s" name (print_type def_type); Env.add env name def_type, def_type

    



