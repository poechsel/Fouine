open Env
open Expr

let int_of_bool b =
  if b then 1 else 0
let bool_of_int x =
  if x = 0 then false
  else true

let interpret program = 
  let rec aux program env =
    match program with
    | Const x -> Const x, env
    | Ident x -> Env.get_most_recent env x, env 
    | Not x -> begin 
        let x', env' = aux x env
        in match x' with
        | Const y -> Const(int_of_bool (y == 0)), env'
        | _ -> failwith "erreur"
      end
    | Add (a, b) -> begin
        let a', env' = aux a env
        in let b', env'' = aux b env'
        in match (a', b') with
        | Const x, Const y -> Const(x + y), env''
        | _ -> failwith "erreur"
      end
    | Minus (a, b) -> begin
        let a', env' = aux a env
        in let b', env'' = aux b env'
        in match (a', b') with
        | Const x, Const y -> Const(x - y), env''
        | _ -> failwith "erreur"
      end
    | Mul (a, b) -> begin
        let a', env' = aux a env
        in let b', env'' = aux b env'
        in match (a', b') with
        | Const x, Const y -> Const(x * y), env''
        | _ -> failwith "erreur"
      end
    | Eq (a, b) -> begin
        let a', env' = aux a env
        in let b', env'' = aux b env'
        in match (a', b') with
        | Const x, Const y -> Const(int_of_bool (x = y)), env''
        | _ -> failwith "erreur"
      end
    | Neq (a, b) -> begin
        let a', env' = aux a env
        in let b', env'' = aux b env'
        in match (a', b') with
        | Const x, Const y -> Const(int_of_bool (x != y)), env''
        | _ -> failwith "erreur"
      end
    | Gt (a, b) -> begin
        let a', env' = aux a env
        in let b', env'' = aux b env'
        in match (a', b') with
        | Const x, Const y -> Const(int_of_bool (x >= y)), env''
        | _ -> failwith "erreur"
      end
    | Sgt (a, b) -> begin
        let a', env' = aux a env
        in let b', env'' = aux b env'
        in match (a', b') with
        | Const x, Const y -> Const(int_of_bool (x > y)), env''
        | _ -> failwith "erreur"
      end
    | Lt (a, b) -> begin
        let a', env' = aux a env
        in let b', env'' = aux b env'
        in match (a', b') with
        | Const x, Const y -> Const(int_of_bool (x <= y)), env''
        | _ -> failwith "erreur"
      end
    | Slt (a, b) -> begin
        let a', env' = aux a env
        in let b', env'' = aux b env'
        in match (a', b') with
        | Const x, Const y -> Const(int_of_bool (x < y)), env''
        | _ -> failwith "erreur"
      end
    | And (a, b) -> begin
        let a', env' = aux a env
        in let b', env'' = aux b env'
        in match (a', b') with
        | Const x, Const y -> Const(int_of_bool (bool_of_int x && bool_of_int y)), env''
        | _ -> failwith "erreur"
      end
    | Or (a, b) -> begin
        let a', env' = aux a env
        in let b', env'' = aux b env'
        in match (a', b') with
        | Const x, Const y -> Const(int_of_bool (bool_of_int x || bool_of_int y)), env''
        | _ -> failwith "erreur"
      end
  (*  | Let (a, b) -> 
      let b', _ =   
*)
    | _ -> failwith "not implemented"

  in aux program (Env.create)
