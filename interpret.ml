open Env
open Expr
open Errors
open Binop
open Lexing
open Prettyprint

(* get all the identifier inside of a tuple *)
let get_id_from_tuple t =
  let rec aux t =
    match t with
    | Tuple (l, _) -> List.fold_left (fun a b ->  a @ aux b)  [] l 
    | Ident(x, _) -> [x]
    | _ -> []
  in aux t 
(* check if a tuple has some identifier that are repeating *)
let tuple_has_double_id t = 
  let rec double_list l = 
    match l with
    | [] -> false
    | x :: t -> List.exists (fun a -> a = x) t || double_list t
  in double_list @@ get_id_from_tuple t

(* get the name of the vars that will be defined if this expression is the left side of a let *)
let rec get_all_ids expr =
  match expr with
  | Ident (x, _) -> [x]
  | Tuple (l, _) -> List.fold_left (fun a b -> a @ get_all_ids b) [] l
  | Constructor(_, expr, _) -> get_all_ids expr
  | _ -> []

(* unify a b will try to unify b with a, and if a match with b will change the environment according to the modification needed in a for havigng a = b*)
let rec unify ident expr env error_infos = 
  match (ident, expr) with
  | Const a, Const b when a = b -> env
  | Underscore, _ -> env
  | Unit, Unit -> env
  | Bool a, Bool b when a = b -> env
  | Ident (x, _), _ -> Env.add env x expr
  | Constructor_noarg(name, er), Constructor_noarg(name', _) ->
    if name = name' then
      env
    else
      raise (send_error (Printf.sprintf "Can't unify constructors %s with %s" name name') er)
  | Constructor(name, expr, er), Constructor(name', expr', _)  ->
    if name = name' then
      unify expr expr' env er
    else
      raise (send_error (Printf.sprintf "Can't unify constructors %s with %s" name name') er)
  | Tuple (l1, error), Tuple (l2, _) ->
    if tuple_has_double_id ident then
      raise (send_error "variable bounded several times in tuple" error)
    else
      let rec aux l1 l2 env =  begin match  (l1, l2) with
        | [], [] -> env
        | x1::t1, x2::t2 -> unify x1 x2 (aux t1 t2 env) error
        | _ -> raise (send_error (Printf.sprintf "Can't unify %s with %s" (pretty_print_aux expr "" true) (pretty_print_aux ident "" true)) error_infos )
      end in aux l1 l2 env
  | _ -> raise (send_error (Printf.sprintf "Can't unify %s with %s" (pretty_print_aux ident "" true) (pretty_print_aux expr "" true)) error_infos )



(* interpret a program. It uses closures, because it is very easy to implement exceptions with them *)
let interpret program env k kE = 
  let env_t = ref env in
  let rec aux env k kE program =
    match program with
    | Underscore  -> k Underscore env
    | Const x -> k (Const x) env
    | Bool x -> k (Bool x) env
    | RefValue (x) -> k program  env
    | Constructor_noarg(name, er) -> k program env 
    | Array _ -> k program env
    | Closure _ -> k program env
    | BuildinClosure _ -> k program env
    | ClosureRec _ -> k program env
    | Ident (x, error_infos) -> 
      let o = try
          Env.get_most_recent env x
        with Not_found ->
          raise  ((send_error ("Identifier '"^x^"' not found") error_infos))
      in k o env
    | Tuple (l, error_infos) ->
      let rec aux_tuple acc l = begin match l with
        | [] -> k (Tuple (List.rev acc, error_infos)) env
        | x::tl -> let k' x' _ =
                     aux_tuple (x'::acc) tl
          in aux env k' kE x
      end in aux_tuple [] l
    | TypeDecl(id, l, error_infos) -> 
      (*let res, env = interpret_type_declaration id l error_infos env
        in let _ = env_t := env
        in k res env*)
      k Unit env
    | Constructor(name, expr, error_infos) ->
      let k' x' _ =
        (* if Env.mem_type env name then *)
        k (Constructor(name, x', error_infos)) env
        (*else
          raise (send_error (Printf.sprintf "Constructor %s not defined" name) error_infos)*)
      in aux env k' kE expr
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
        let nenv = unify a b' env error_infos
        in let _ = env_t := nenv
        in k b' nenv
      in aux env k' kE b
    | LetRec(a, b, error_infos) -> 
      begin match a with
        | Ident(x, _) ->
          begin match b with

            | Fun (id, expr, _) -> 
              let clos = (ClosureRec(x, id, expr, env)) (*recursive closure are here to allow us to add the binding of id with expr at the last moment *)
              in let _ = env_t := (Env.add env x clos )
              in k clos !env_t
            | _ -> let k' b' _ = 
                     let _ = env_t := (unify a b' env error_infos)
                     in k b' !env_t
              in aux env k' kE b
          end

        | _ -> raise (send_error "a function declaration must begin by an id" error_infos)
      end
    (*begin
      match b with
      | Fun (id, expr, _) -> 
        begin match a with
          | Ident(x, _) ->
            let clos = (ClosureRec(x, id, expr, env)) (*recursive closure are here to allow us to add the binding of id with expr at the last moment *)
            in let _ = env_t := (Env.add env x clos )
      in k clos !env_t
          | _ -> raise (send_error "a function declaration must begin by an id" error_infos)
        end
      | _ -> let k' b' _ = 
               let _ = env_t := (unify a b' env error_infos)
               in k b' !env_t
        in aux env k' kE b
                                   end*)


    | In(_, Let(_), error_infos) -> raise (send_error "An 'in' clause can't end with a let. It must returns something" error_infos)
    | MainSeq(a, b, error_infos) | Seq(a, b, error_infos) ->
      let temp = ref env in 
      let k' a' env' = 
        aux env' k kE b (* why ref? just because we need the secondone to be a copy of the env of the firstone *)
      in aux env k' kE a
    | In (a, b, error_infos) -> 
      begin match a with
        | LetRec (Ident (x, _), Fun (arg, expr, _), _) ->
          let clos = (ClosureRec(x, arg, expr, env))
          in aux (Env.add env x clos) k kE b
        | Let (a, expr, error_infos) -> 
          let k' expr' _ = 
            aux (unify a expr' env error_infos) k kE b
          in aux env k' kE expr
        | _ -> raise (send_error "incorrect in" error_infos)
      end
      (*
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
*)
    | Fun (id, expr, error_infos) -> 
      k (Closure(id, expr, env)) env
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
            | Constructor_noarg (name, er) ->
              aux env k kE (Constructor(name, arg', er)) 
            | BuildinClosure (fct) ->
              k (fct arg') env
            | Closure (key, expr, env_fct) ->
              aux (unify key arg' env_fct error_infos) k kE expr
            | ClosureRec(key, arg_key, expr, env_fct) ->
              let env_fct = Env.add env_fct key fct'
              in let env_fct = unify arg_key arg' env_fct error_infos
              in aux env_fct k kE expr
            | _ -> raise (send_error "You are probably calling a function with too much parameters " error_infos)

          end
        in aux env k' kE arg
      in aux env k'' kE fct
    | Printin(expr, error_infos) -> 
      let k' a _ = 
        begin
          match a with
          | Const x ->  let _ = Printf.printf "%d\n" x in k (Const(x)) env
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

    | MatchWith (expr, match_list, error ) ->
      let k' expr' _ = 
        let rec aux_match l =
          match l with
          | (pattern, action)::tl ->
            begin
              try
                let env' = unify pattern expr' env error
                in aux env' k kE action
              with InterpretationError _ ->
                aux_match tl
            end
          | [] -> raise (send_error (Printf.sprintf "Didn't match the expr : %s" (pretty_print expr')) error)
        in aux_match match_list

      in aux env k' kE expr


    | _ -> raise (send_error "You encountered something we can't interpret. Sorry" (Lexing.dummy_pos))

  in let e,x = aux env k kE program
  in e, !env_t

