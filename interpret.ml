open Env
open Expr
open Binop

let interpret program k kE = 
  let rec aux env k kE program =
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
    | Const x -> k (Const x) env
    | Ident x -> let o = Env.get_most_recent env x 
   (*   in let _ = Printf.printf "%s : %s\n" x (beautyfullprint o)
     *) in k o env 
    | Unit -> k Unit env
    | Not x -> 
      let k' x' env' =
      begin 
        match x' with
        | Const y -> k (Const(int_of_bool (y == 0))) env'
        | _ -> failwith "erreur"
      end
      in aux env k' kE x
    | BinOp(x, a, b) -> 
      let k'' b' env''=
          let k' a' env' = 
            k (x#interpret a' b') env
          in aux env k' kE a 
      in aux env k'' kE b


    | Let (a, b) -> 
      let k' b' env' =
      begin match a with
      | Ident(x) -> k Unit (Env.add env x b')
      | _ -> failwith "not an identificator"
      end
      in aux env k' kE b
   | LetRec (Ident(x), b) -> begin
            match b with
            | Fun (id, expr) -> k Unit (Env.add env x (ClosureRec(x, id, expr, env)))
            | _ -> Unit, env
        end
    | In (a, b) -> 
        let k' a' env' = 
          aux env' k kE b
        in aux env k' kE a
    | Fun (id, expr) -> 
      begin
        match id with
        | Ident(x) ->  k (Closure(id, expr, env)) env
        | _ -> failwith "bad identifier for a variable"
      end
    | IfThenElse(cond, a, b) ->
      let k' cond' env' = 
        begin 
          match (cond') with
          | Const 0 -> aux env' k kE b
          | Const x -> aux env' k kE a
          | _ -> failwith ("error in condition")
        end
      in aux env k' kE cond
    | Call(fct, arg) -> 
      let k'' fct' env'' = 
        let k' arg' env' =
          begin match (fct') with
            | Closure(Ident(id), expr, env) -> 
              let new_env = Env.add env id arg'
              in aux new_env k kE expr
            | ClosureRec(key, Ident(id), expr, env) ->
              let new_env = Env.add env id arg'
              in aux (Env.add new_env key fct') k kE expr
            | _ -> failwith "oupsi"
                     end
        in aux env'' k' kE arg
      in aux env k'' kE fct
      
     (*) 
      begin
        let fct', _ = aux fct env
        in match (fct') with
        | Closure(Ident(id), expr, env') -> 
          let arg', _ = aux arg env
          in let env'' = Env.add env' id arg'
          in aux expr env''
       *)
(*        | ClosureRec(key, Ident(id), expr, env') -> 
          let arg', _ = aux arg env
          in let env'' = Env.add env' id arg'
          in aux expr (Env.add env'' key fct')
            
        | _ ->  failwith "we can't call something that isn't a function"
          end *)
    | Printin(expr) -> 
        let k' a env' = 
    begin
        match a with
            | Const x -> print_int x;print_newline(); k (Const(x)) env
            | _ -> failwith "not an int"
    end 
        in aux env k' kE expr
    | _ -> failwith "not implemented"

  in aux (Env.create) k kE program
