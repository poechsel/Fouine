open Env
open Expr
open Errors
open Binop
open Lexing
open Prettyprint

let testfct x env k kE = 
  match x with
  | Const y -> print_string @@ string_of_int y; k Unit env
  | _ -> failwith ("type")
(*)

let interpret program env =
  let rec aux program env =
    match program with
    | Underscore  -> Underscore , env
    | Const x ->  (Const x), env
    | Bool x ->  (Bool x), env
    | Ident (x, error_infos) -> 
      let o = try
          Env.get_most_recent env x
        with Not_found ->
          raise  ((send_error ("Identifier '"^x^"' not found") error_infos))
      in  o, env
    | Unit ->  Unit, env
    | Bang (x, error_infos) ->
      let x', _ = aux x env
      in begin
          match x' with
          | RefValue y -> !y, env
          | _ -> raise (send_error "Can't deref a non ref value" error_infos)
        end 
    | Ref (x, error_infos) ->
      let x, _ = aux x env
       in  (RefValue (ref x)), env
    | Not (x, error_infos) -> 
      let x', _ = aux x env
      in 
        begin 
          match x' with
          | Bool y -> (Bool (not y)), env
          | _ -> raise (send_error "Not operations can only be made on boolean values" error_infos)
        end
    | BinOp(x, a, b, error_infos) -> 
      let a', _ = aux a env
      in let b', _ = aux b env
      in x#interpret a' b' error_infos, env
    | Let (a, b, error_infos) -> 
      let b', _ = aux b env
      in
        begin match a with
          | Ident(x, _) -> b', (Env.add env x b')
          | Underscore -> b', env
          | _ -> raise (send_error "The left side of an affectation must be an identifier or an underscore" error_infos)
        end
    | LetRec(Underscore, b, e) -> aux (Let(Underscore, b, e)) env
    | LetRec (Ident(x, temp), b, error_infos) -> begin
        match b with
        | Fun (id, expr, _) -> let clos = (ClosureRec(x, id, expr, env)) (*recursive closure are here to allow us to add the binding of id with expr at the last moment *)
          in clos, (Env.add env x clos )
        | _ -> aux (Let (Ident(x, temp), b, error_infos)) env (*let rec constant is the same than a let rec*)
      end
    | In(_, Let(_), error_infos) -> raise (send_error "An 'in' clause can't end with a let. It must returns something" error_infos)
    | MainSeq(a, b, error_infos) | Seq(a, b, error_infos) ->
      aux b (snd @@ aux a  env)
    | In (a, b, error_infos) -> 
      let a', env' = aux a env
      in 
        begin match (a) with
          | Let(Ident(x, _), _, _) -> let o, _ = aux b env' in o, env
          | LetRec(Ident(x, _), _, _) -> let o, _ = aux b env' in o, env
          | _ -> aux b env'
        end 
    | Fun (id, expr, error_infos) -> 
      begin
        match id with
        | Ident(x, _) ->  (Closure(id, expr, env)), env
        | Unit | Underscore -> (Closure(Unit, expr, env)), env
        | _ -> raise (send_error "An argument name must be an identifier" error_infos)
      end
    | IfThenElse(cond, a, b, error_infos) ->
      let cond', _ = aux cond env
      in 
        begin 
          match (cond') with
          | Bool false -> let o, _ = aux b env in o, env
          | Bool true -> let o, _ = aux a env in o , env
          | _ -> raise (send_error "In a If clause the condition must return a boolean" error_infos)
        end
    | Call(fct, arg, error_infos) -> 
        let fct', _ = aux fct env in 
        let arg', _ = aux arg env in
        let o, env = begin match (fct') with
            | BuildinClosure (fct) ->
              let o, _ = aux (fct arg') env in o, env
            | Closure(Ident(id, _), expr, envc) -> 
              let out, _ = aux expr (Env.add envc id arg')
              in out, env
            | Closure(Unit, expr, envc) | Closure(Underscore, expr, envc) -> 
                let o, _ = aux expr envc in o, env
            | ClosureRec(key, Ident(id, _), expr, envc) ->
              let new_env = Env.add envc id arg'
              in let o, _ =  aux expr (Env.add new_env key fct') 
              in o, env
            | ClosureRec(key, Unit, expr, envc) | ClosureRec(key, Underscore, expr, envc)->
              let o, _ = aux expr (Env.add envc key fct') 
              in o, env
            | _ -> raise (send_error "You are probably calling a function with too much parameters" error_infos)
            end
        in o, env
    | Printin(expr, error_infos) -> 
      let a, _ = aux expr env in
        begin
          match a with
          | Const x -> print_int x;print_newline(); (Const(x)), env
          | _ -> raise (send_error "This function is called 'prInt'. How could it work on non-integer values" error_infos)
        end 
        (*
    | Raise (e, error_infos) ->
      let o, _ = 
     begin
       except := Except 
      aux env kE kE e
(* we have two try with syntaxes: one with matching, the other without *)
    | TryWith (t_exp, Ident(x, _), w_exp, error_infos) ->
      let kE' t_exp' env' =
        aux (Env.add env x t_exp')  k kE w_exp 
      in aux env k kE' t_exp
    | TryWith (t_exp, Const(er), w_exp, error_infos) ->
      let kE' t_exp' env' =
        match (t_exp') with
        | Const(v) when v = er -> aux env k kE w_exp 
        | _ -> aux env k kE t_exp

      in aux env k kE' t_exp

  *)  | ArrayMake (expr, error_infos) ->
      let a, _ = aux expr env in
        begin
          match a with
          | Const x when x < 0 -> raise (send_error (Printf.sprintf "The size (%d) of this array will be negative" x) error_infos)
          | Const x -> (Array (Array.make x 0)), env
          | _ -> raise (send_error "An array must have an integer size" error_infos)
        end 

    | ArrayItem (id, expr, error_infos) ->
      let id', _ = aux id env in
      let expr', _ = aux expr env in
          begin match (id', expr') with
            | Array (x), Const (i) -> 
              if i < 0 || i >= Array.length x then
                raise (send_error ((Printf.sprintf "You are accessing element %d of an array of size %d") i (Array.length x)) error_infos)
              else 
                (Const x.(i)), env
            | a, b -> raise (send_error ("Bad way to access an array") error_infos)
          end 


    | ArraySet (id, expr, nvalue, error_infos) ->
      let nvalue', _ = aux nvalue env in
      let id', _ = aux id env in
      let expr', _ = aux expr env in
            begin match (id', expr', nvalue') with
              | Array (x), Const (i), Const(y) -> (* pensez à ajouter la generation d'exceptions aprés coup *)
                if i < 0 || i >= Array.length x then
                  raise (send_error ((Printf.sprintf "You are accessing element %d of an array of size %d") i (Array.length x)) error_infos)
                else 
                  x.(i) <- y; (Unit), env
              | _ -> raise (send_error "When seting the element of an array, the left side must be an array, the indices an integer and the value an integer" error_infos)
            end 
    | _ -> raise (send_error "You encountered something we can't interpret. Sorry" (Lexing.dummy_pos))

  in aux program env


*)
(* interpret a program. It uses closures, because it is very easy to implement exceptions with them *)
let interpret program env k kE = 
  let rec aux env k kE program =
    match program with
    | Underscore  -> k Underscore env
    | Const x -> k (Const x) env
    | Bool x -> k (Bool x) env
    | Ident (x, error_infos) -> 
      let o = try
          Env.get_most_recent env x
        with Not_found ->
          raise  ((send_error ("Identifier '"^x^"' not found") error_infos))
      in k o env
    | Unit -> k Unit env
    | Bang (x, error_infos) ->
      let k' x' _ = 
        begin
          match x' with
          | RefValue y -> k !y env
          | _ -> raise (send_error "Can't deref a non ref value" error_infos)
        end 
      in aux env k' kE x
    | Ref (x, error_infos) ->
      let k' x' _ =
        k (RefValue (ref x')) env
      in aux env k' kE x
    | Not (x, error_infos) -> 
      let k' x' _ =
        begin 
          match x' with
          | Bool y -> k (Bool (not y)) env
          | _ -> raise (send_error "Not operations can only be made on boolean values" error_infos)
        end
      in aux env k' kE x
    | BinOp(x, a, b, error_infos) -> 
      let k'' b' _ =
        let k' a' _ = 
          k (x#interpret a' b' error_infos) env
        in aux env k' kE a 
      in aux env k'' kE b
    | Let (a, b, error_infos) -> 
      let k' b' _ =
        begin match a with
          | Ident(x, _) -> k b' (Env.add env x b')
          | Underscore -> k b' env
          | _ -> raise (send_error "The left side of an affectation must be an identifier or an underscore" error_infos)
        end
      in aux env k' kE b
    | LetRec(Underscore, b, e) -> aux env k kE (Let(Underscore, b, e))
    | LetRec (Ident(x, temp), b, error_infos) -> begin
        match b with
        | Fun (id, expr, _) -> let clos = (ClosureRec(x, id, expr, env)) (*recursive closure are here to allow us to add the binding of id with expr at the last moment *)
          in k clos (Env.add env x clos )
        | _ -> aux env k kE (Let (Ident(x, temp), b, error_infos)) (*let rec constant is the same than a let rec*)
      end
    | In(_, Let(_), error_infos) -> raise (send_error "An 'in' clause can't end with a let. It must returns something" error_infos)
    | MainSeq(a, b, error_infos) | Seq(a, b, error_infos) ->
      let k' a' env' = 
        aux env' k kE b
      in aux env k' kE a
    | In (a, b, error_infos) -> 
      begin match a with
        | LetRec(Underscore, expr, _) | Let (Underscore, expr, _) ->
          let k' c _ =
            aux env k kE b
          in aux env k' kE expr
        | LetRec (Ident (x, _) as fn_id, Fun (arg, expr, _), _ ) ->
            let clos = (ClosureRec(x, arg, expr, env))
            in aux (Env.add env x clos) k kE b
        | LetRec (Ident (x, _), expr, _) | Let (Ident(x, _), expr, _) -> 
          let k' c _ =
            let env' = Env.add env x c
            in aux env' k kE b
          in aux env k' kE expr
        | LetRec (_, _, error_infos) | Let (_, _, error_infos) -> raise (send_error "The left side of an affectation must be an identifier or an underscore" error_infos)
        | _ -> raise (send_error "incorrect in" error_infos)


            end
      (*
      let k' a' env' = 
        let out, nenv = aux env' k kE b
        in begin match (a) with
          | Let(Ident(x, _), _, _) -> Printf.printf "out -> %s\n" (pretty_print out);k out env (* after executing a let a = foo in expr, a is not added to the scope *)
          | LetRec(Ident(x, _), _, _) -> k out env
          | _ -> k out nenv
        end 
      in aux env k' kE a
        *)
    | Fun (id, expr, error_infos) -> 
      begin
        match id with
        | Ident(x, _) ->  k (Closure(id, expr, env)) env
        | Unit | Underscore -> k (Closure(Unit, expr, env)) env
        | _ -> raise (send_error "An argument name must be an identifier" error_infos)
      end
    | IfThenElse(cond, a, b, error_infos) ->
      let k' cond' _ = 
        begin 
          match (cond') with
          | Bool false -> aux env k kE b
          | Bool true -> aux env k kE a
          | _ -> raise (send_error "In a If clause the condition must return a boolean" error_infos)
        end
      in aux env k' kE cond
    | Call(fct, arg, error_infos) -> 
      let k'' fct' _ =
        let k' arg' _ =
          begin match (fct') with 
            | ClosureRec(key, Ident(id, _), expr, env_fct) ->
              let env_fct = Env.add env_fct key fct'
              in let env_fct = Env.add env_fct id arg'
              in aux env_fct k kE expr
            | Closure(Ident(id, _), expr, env_fct) ->
                let env_fct = Env.add env_fct id arg'
                in aux env_fct k kE expr
            | Closure(Unit, expr, env_fct) | Closure(Underscore, expr, env_fct) ->
              aux env_fct k kE expr
            | ClosureRec(key, Unit, expr, env_fct) | ClosureRec(key, Underscore, expr, env_fct) ->
              aux (Env.add env_fct key fct') k kE expr
            | _ -> Printf.printf "bug %s" (pretty_print fct');raise (send_error "You are probably calling a function with too much parameters" error_infos)

          end
        in aux env k' kE arg

      in aux env k'' kE fct
      (*

      let k'' fct' env'' = 
        let k' arg' env' =
          begin match (fct') with
            | BuildinClosure (fct) ->
              aux env k kE (fct arg')
            | Closure(Ident(id, _), expr, env) -> 
              let new_env = Env.add env id arg'
              in let out, nenv = aux new_env k kE expr
              in k out env
            | Closure(Unit, expr, env) | Closure(Underscore, expr, env) -> 
              aux env k kE expr
            | ClosureRec(key, Ident(id, _), expr, env) ->
              let new_env = Env.add env id arg'
              in aux (Env.add new_env key fct') k kE expr
            | ClosureRec(key, Unit, expr, env) | ClosureRec(key, Underscore, expr, env)->
              aux (Env.add env key fct') k kE expr
            | _ -> Printf.printf "bug %s" (pretty_print fct');raise (send_error "You are probably calling a function with too much parameters" error_infos)
            end
        in aux env k' kE arg
      in aux env k'' kE fct
*)
    | Printin(expr, error_infos) -> 
      let k' a _ = 
        begin
          match a with
          | Const x -> print_int x;print_newline(); k (Const(x)) env
          | _ -> raise (send_error "This function is called 'prInt'. How could it work on non-integer values" error_infos)
        end 
      in aux env k' kE expr
    | Raise (e, error_infos) ->
      aux env kE kE e
(* we have two try with syntaxes: one with matching, the other without *)
    | TryWith (t_exp, Ident(x, _), w_exp, error_infos) ->
      let kE' t_exp' _ =
        aux (Env.add env x t_exp')  k kE w_exp 
      in aux env k kE' t_exp
    | TryWith (t_exp, Const(er), w_exp, error_infos) ->
      let kE' t_exp' _ =
        match (t_exp') with
        | Const(v) when v = er -> aux env k kE w_exp 
        | _ -> aux env k kE t_exp

      in aux env k kE' t_exp

    | ArrayMake (expr, error_infos) ->
      let k' a _ = 
        begin
          match a with
          | Const x when x < 0 -> raise (send_error (Printf.sprintf "The size (%d) of this array will be negative" x) error_infos)
          | Const x -> k (Array (Array.make x 0)) env
          | _ -> raise (send_error "An array must have an integer size" error_infos)
        end 
      in aux env k' kE expr

    | ArrayItem (id, expr, error_infos) ->
      let k'' id' _ =
        let k' expr' _ = 
          begin match (id', expr') with
            | Array (x), Const (i) -> 
              if i < 0 || i >= Array.length x then
                raise (send_error ((Printf.sprintf "You are accessing element %d of an array of size %d") i (Array.length x)) error_infos)
              else 
                k (Const x.(i)) env
            | a, b -> raise (send_error ("Bad way to access an array") error_infos)
          end 
        in aux env k' kE expr
      in aux env k'' kE id


    | ArraySet (id, expr, nvalue, error_infos) ->
      let k_value nvalue' _ = 
        let k'' id' _ =
          let k' expr' _ = 
            begin match (id', expr', nvalue') with
              | Array (x), Const (i), Const(y) -> (* pensez à ajouter la generation d'exceptions aprés coup *)
                if i < 0 || i >= Array.length x then
                  raise (send_error ((Printf.sprintf "You are accessing element %d of an array of size %d") i (Array.length x)) error_infos)
                else 
                  x.(i) <- y; k (Unit) env
              | _ -> raise (send_error "When seting the element of an array, the left side must be an array, the indices an integer and the value an integer" error_infos)
            end 
          in aux env k' kE expr
        in aux env k'' kE id
      in aux env k_value kE nvalue

    | _ -> raise (send_error "You encountered something we can't interpret. Sorry" (Lexing.dummy_pos))

  in aux env k kE program

