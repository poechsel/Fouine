open Env
open Expr

let int_of_bool b =
  if b then 1 else 0
let bool_of_int x =
  if x = 0 then false
  else true

let interpret program = 
  let rec aux program env =
    (*
    let _ = match program with
      | Const x -> print_endline "const"
      | Ident x -> print_endline @@"ident: "^x
      | Mul (_,_) -> print_endline "*"
      | Eq(_, _) -> print_endline "="
      | In(_, _) -> print_endline "in"
      | LetRec(_, _) -> print_endline "let rec"
      | Fun(_, _) -> print_endline "fun"
      | IfThenElse(_, _, _)->print_endline "ifthenelse"
      | Closure(_, _, _)->print_endline "closure"
      | ClosureRec(_, _, _, _)->print_endline "closurerec"
      | _ -> ()
in


*)
    match program with
    | Const x -> Const x, env
    | Ident x -> let o = Env.get_most_recent env x 
   (*   in let _ = Printf.printf "%s : %s\n" x (beautyfullprint o)
     *) in o, env 
    | Unit -> Unit, env
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
    | Let (a, b) -> 
      let b', _ =  aux b env
      in begin match a with
      | Ident(x) -> (Unit, Env.add env x b')
      | _ -> failwith "not an identificator"
        end
    | LetRec (Ident(x), b) -> begin
            match b with
            | Fun (id, expr) -> Unit, Env.add env x (ClosureRec(x, id, expr, env))
            | _ -> Unit, env
        end
    | In (a, b) -> 
      let _, env' = aux a env
      in aux b env' 
    | Fun (id, expr) -> begin
        match id with
        | Ident(x) -> Closure(id, expr, env), env
        | _ -> failwith "bad identifier for a variable"
      end
    | IfThenElse(cond, a, b) ->
      let cond', env' = aux cond env
      in begin 
        match (cond') with
        | Const 0 -> aux b env'
        | Const x -> aux a env'
        | _ -> failwith ("error in condition")
      end
    | Call(fct, arg) -> begin
        let fct', _ = aux fct env
        in match (fct') with
        | Closure(Ident(id), expr, env') -> 
          let arg', _ = aux arg env
          in let env'' = Env.add env' id arg'
          in aux expr env''
        | ClosureRec(key, Ident(id), expr, env') -> 
          let arg', _ = aux arg env
          in let env'' = Env.add env' id arg'
          in aux expr (Env.add env'' key fct')
        | Fun(Ident(x), expr) -> failwith "a"
        | _ ->  failwith "we can't call something that isn't a function"
        end
    | Printin(expr) -> 
        let a, env'= aux expr env in
    begin
        match a with
            | Const x -> print_int x;print_newline(); Const(x), env
            | _ -> failwith "not an int"
end 
    | _ -> failwith "not implemented"

  in aux program (Env.create)
