open Expr
open Env
type type_listing =
    | No_type
   | Int_type
   | Bool_type
   | Array_type
   | Unit_type
   | Var_type of type_listing
   | Ref_type of type_listing
   | Fun_type of type_listing * type_listing

let rec print_type t = match t with
  | Int_type -> "int"
  | Bool_type -> "bool"
  | Array_type -> "array"
  | Unit_type -> "unit"
  | Var_type No_type -> "'a"
  | Var_type x -> print_type x
  | Fun_type (a, b) -> Printf.sprintf ("%s -> %s") (print_type a) (print_type b)
  | _ -> ""

let rec prune t = 
  match t with
  | Var_type No_type -> t
  | Var_type x -> Var_type (prune t)
  | _ -> t 

let rec occurs_in v t = 
  match v, t with
  | Int_type, Int_type -> true
  | Bool_type, Bool_type -> true
  | Array_type, Array_type -> true
  | Unit_type, Unit_type -> true
  | _, Var_type x -> occurs_in v (prune x)
  | _, Fun_type (a, b) -> occurs_in v (prune a) || occurs_in v (prune b)
  | _ -> false

let rec unify t1 t2 =
  let rec aux t1 t2 =
    match (t1, t2) with
    | Int_type, Int_type -> Int_type
    | Bool_type, Bool_type -> Bool_type
    | Array_type, Array_type -> Array_type
    | Unit_type, Unit_type -> Unit_type
    | Var_type x, _ -> if occurs_in t1 t2 then failwith "rec" else Var_type t2
    | Fun_type _, Var_type _-> unify t2 t1
    | Fun_type (a, b), Fun_type (a', b') ->
      Fun_type (unify a a', unify b b')
    | _, _ -> failwith "unify bug"
  in aux (prune t1) (prune t2)



let rec analyse node env non_generic =
  match node with
  | Unit -> env, Unit_type
  | Bool _ -> env, Bool_type
  | Const _ -> env, Int_type
  | Ident (x, _) -> env, Env.get_most_recent env x
  | Call(arg, what, _ ) -> 
    let _, fun_type = analyse what env non_generic
    in let _, arg_type = analyse arg env non_generic
    in env, unify (Fun_type (arg_type, (Var_type No_type))) fun_type
  | Fun (Ident(x, _), expr, _) ->
    let  arg_type = Var_type (No_type)
    in let env' = Env.add env x arg_type
in let ng' = (arg_type) :: non_generic
in env, Fun_type (arg_type, snd @@ analyse expr env' ng')
  | Let(Ident(name, _), what, _ ) -> 
    let _, def_type = analyse what env non_generic
    in Printf.sprintf "%s : %s" name (print_type def_type); Env.add env name def_type, def_type

    



