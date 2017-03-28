open Env
open Expr
open Binop

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
    | BinOp(x, a, b) -> 
      let a', env' = aux a env
      in let b', env' = aux b env
      in x#interpret a' b', env'
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
