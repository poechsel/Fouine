open Env
open Expr
open Binop
open Lexing

exception InterpretationError of string
let send_error str infos = 
 (str ^ (string_of_int (infos.pos_lnum)))

let interpret program env k kE = 
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
    | Underscore  -> k Underscore env
    | Const x -> k (Const x) env
    | Ident x -> let o = try
        Env.get_most_recent env x
      with Not_found ->
           raise  (InterpretationError (send_error ("identifier "^x^" not found") (Lexing.dummy_pos )))
      in k o env
   (*   in let _ = Printf.printf "%s : %s\n" x (beautyfullprint o)

     *) 
    | Unit -> k Unit env
    | Bang (x, error_infos) ->
      let k' x' env' = 
        begin
          match x' with
          | RefValue y -> k !y env'
          | _ -> failwith "can't deref a non ref value"
        end 
      in aux env k' kE x
    | Ref (x, error_infos) ->
      let k' x' env' =
        k (RefValue (ref x')) env'
      in aux env k' kE x
    | Not (x, error_infos) -> 
      let k' x' env' =
      begin 
        match x' with
        | Const y -> k (Const(int_of_bool (y == 0))) env'
        | _ -> failwith "erreur"
      end
      in aux env k' kE x
    | BinOp(x, a, b, error_infos) -> 
      let k'' b' env''=
          let k' a' env' = 
            k (x#interpret a' b') env
          in aux env k' kE a 
      in aux env k'' kE b


    | Let (a, b, error_infos) -> 
      let k' b' env' =
      begin match a with
      | Ident(x) -> k Unit (Env.add env x b')
      | Underscore -> k Underscore env
      | _ -> failwith "not an identificator"
      end
      in aux env k' kE b
   | LetRec (Ident(x), b, error_infos) -> begin
            match b with
            | Fun (id, expr, _) -> k Unit (Env.add env x (ClosureRec(x, id, expr, env)))
            | Underscore -> k Underscore env
            | _ -> Unit, env
        end
    | In (a, b, error_infos) -> 
        let k' a' env' = 
            let out, nenv = aux env' k kE b
            in begin match (a) with
            | Let(Ident(x), _, _) -> out, env
            | _ -> out, nenv
            end 
            in aux env k' kE a
    | Fun (id, expr, error_infos) -> 
      begin
        match id with
        | Ident(x) ->  k (Closure(id, expr, env)) env
        | _ -> failwith "bad identifier for a variable"
      end
    | IfThenElse(cond, a, b, error_infos) ->
      let k' cond' env' = 
        begin 
          match (cond') with
          | Const 0 -> aux env' k kE b
          | Const x -> aux env' k kE a
          | _ -> failwith ("error in condition")
        end
      in aux env k' kE cond
    | Call(fct, arg, error_infos) -> 
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
      
    | Printin(expr, _) -> 
      let k' a env' = 
        begin
          match a with
          | Const x -> print_int x;print_newline(); k (Const(x)) env'
          | _ -> failwith "not an int"
        end 
      in aux env k' kE expr
    | Raise (e, error_infos) ->
      aux env kE kE e
    | TryWith (t_exp, Const(er), w_exp, error_infos) ->
      let kE' t_exp' env' =
        match (t_exp') with
        | Const(v) when v = er -> aux env k kE w_exp 
        | _ -> k Unit env'

      in aux env k kE' t_exp

    | ArrayMake (expr, error_infos) ->
      let k' a env' = 
        begin
          match a with
          | Const x -> k (Array (Array.make x 0)) env'
          | _ -> failwith "can't create an array of size which isn't an int"
        end 
      in aux env k' kE expr

    | ArrayItem (id, expr, error_infos) ->
      let k'' id' env'' =
        let k' expr' env' = 
          begin match (id', expr') with
            | Array (x), Const (i) -> (* pensez à ajouter la generation d'exceptions aprés coup *)
              k (Const x.(i)) env'
            | _ -> failwith "bad way to access an array"
          end 
        in aux env'' k' kE expr
      in aux env k'' kE id


    | ArraySet (id, expr, nvalue, error_infos) ->
      let k_value nvalue' nenv = 
        let k'' id' env'' =
          let k' expr' env' = 
            begin match (id', expr', nvalue') with
              | Array (x), Const (i), Const(y) -> (* pensez à ajouter la generation d'exceptions aprés coup *)
                x.(i) <- y; k (Const y) env'
              | _ -> failwith "bad way to affect an array"
            end 
          in aux env'' k' kE expr
        in aux nenv k'' kE id
      in aux env k_value kE nvalue

    | _ -> failwith "not implemented"

  in aux env k kE program
