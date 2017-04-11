open Env
open Expr
open Errors
open Binop
open Lexing

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
      let k' x' env' = 
        begin
          match x' with
          | RefValue y -> k !y env'
          | _ -> raise (send_error "Can't deref a non ref value" error_infos)
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
          | Bool y -> k (Bool (not y)) env'
          | _ -> raise (send_error "Not operations can only be made on boolean values" error_infos)
        end
      in aux env k' kE x
    | BinOp(x, a, b, error_infos) -> 
      let k'' b' env''=
        let k' a' env' = 
          k (x#interpret a' b' error_infos) env
        in aux env k' kE a 
      in aux env k'' kE b
    | Let (a, b, error_infos) -> 
      let k' b' env' =
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
    | MainSeq(a, b, error_infos) ->
      let k' a' env' = 
        aux env' k kE b
      in aux env k' kE a
    | Seq(a, b, error_infos) ->
      let k' a' env' = 
        aux env' k kE b
      in aux env k' kE a
    | In (a, b, error_infos) -> 
      let k' a' env' = 
        let out, nenv = aux env' k kE b
        in begin match (a) with
          | Let(Ident(x, _), _, _) -> out, env (* after executing a let a = foo in expr, a is not added to the scope *)
          | LetRec(Ident(x, _), _, _) -> out, env
          | _ -> out, nenv
        end 
      in aux env k' kE a
    | Fun (id, expr, error_infos) -> 
      begin
        match id with
        | Ident(x, _) ->  k (Closure(id, expr, env)) env
        | Unit | Underscore -> k (Closure(Unit, expr, env)) env
        | _ -> raise (send_error "An argument name must be an identifier" error_infos)
      end
    | IfThenElse(cond, a, b, error_infos) ->
      let k' cond' env' = 
        begin 
          match (cond') with
          | Bool false -> aux env' k kE b
          | Bool true -> aux env' k kE a
          | _ -> raise (send_error "In a If clause the condition must return a boolean" error_infos)
        end
      in aux env k' kE cond
    | Call(fct, arg, error_infos) -> 
      let k'' fct' env'' = 
        let k' arg' env' =
          begin match (fct') with
            | Closure(Ident(id, _), expr, env) -> 
              let new_env = Env.add env id arg'
              in let x, e = aux new_env k kE expr
              in x, env'
            | Closure(Unit, expr, env) | Closure(Underscore, expr, env) -> 
              let x, e = aux env k kE expr
              in x, env'
            | ClosureRec(key, Ident(id, _), expr, env) ->
              let new_env = Env.add env id arg'
              in let x, e = aux (Env.add new_env key fct') k kE expr
              in x, env'
            | ClosureRec(key, Unit, expr, env) | ClosureRec(key, Underscore, expr, env)->
              let x, e = aux (Env.add env key fct') k kE expr
              in x, env'
            | _ -> raise (send_error "You are probably calling a function with too much parameters" error_infos)
          end
        in aux env k' kE arg
      in let x, _ = aux env k'' kE fct
      in x, env

    | Printin(expr, error_infos) -> 
      let k' a env' = 
        begin
          match a with
          | Const x -> print_int x;print_newline(); k (Const(x)) env'
          | _ -> raise (send_error "This function is called 'prInt'. How could it work on non-integer values" error_infos)
        end 
      in aux env k' kE expr
    | Raise (e, error_infos) ->
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

    | ArrayMake (expr, error_infos) ->
      let k' a env' = 
        begin
          match a with
          | Const x when x < 0 -> raise (send_error (Printf.sprintf "The size (%d) of this array will be negative" x) error_infos)
          | Const x -> k (Array (Array.make x 0)) env'
          | _ -> raise (send_error "An array must have an integer size" error_infos)
        end 
      in aux env k' kE expr

    | ArrayItem (id, expr, error_infos) ->
      let k'' id' env'' =
        let k' expr' env' = 
          begin match (id', expr') with
            | Array (x), Const (i) -> 
              if i < 0 || i >= Array.length x then
                raise (send_error ((Printf.sprintf "You are accessing element %d of an array of size %d") i (Array.length x)) error_infos)
              else 
                k (Const x.(i)) env'
            | a, b -> raise (send_error ("Bad way to access an array") error_infos)
          end 
        in aux env'' k' kE expr
      in aux env k'' kE id


    | ArraySet (id, expr, nvalue, error_infos) ->
      let k_value nvalue' nenv = 
        let k'' id' env'' =
          let k' expr' env' = 
            begin match (id', expr', nvalue') with
              | Array (x), Const (i), Const(y) -> (* pensez à ajouter la generation d'exceptions aprés coup *)
                if i < 0 || i >= Array.length x then
                  raise (send_error ((Printf.sprintf "You are accessing element %d of an array of size %d") i (Array.length x)) error_infos)
                else 
                  x.(i) <- y; k (Unit) env'
              | _ -> raise (send_error "When seting the element of an array, the left side must be an array, the indices an integer and the value an integer" error_infos)
            end 
          in aux env'' k' kE expr
        in aux nenv k'' kE id
      in aux env k_value kE nvalue

    | _ -> raise (send_error "You encountered something we can't interpret. Sorry" (Lexing.dummy_pos))

  in aux env k kE program
