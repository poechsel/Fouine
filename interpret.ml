open Shared
open Expr
open Errors
open Binop
open Lexing
open Prettyprint
open Shared.Env

(* get all the identifier inside of a tuple *)
let get_id_from_tuple t =
  let rec aux t =
    match t with
    | Tuple (l, _) -> List.fold_left (fun a b ->  a @ aux b)  [] l 
    | FixedType(t, _, _) -> aux t
    | Ident (t, _) -> [t]
    | _ -> []
  in aux t 
(* check if a tuple has some identifier that are repeating *)
let tuple_has_double_id t = 
  let rec double_list l = 
    match l with
    | [] -> false
    | x :: t -> List.exists (fun a -> a = x) t 
                || double_list t
  in double_list @@ get_id_from_tuple t

(* get the name of the vars that will be defined if this expression is the left side of a let *)
let rec get_all_ids expr =
  match expr with
  | Ident (t, _) -> [t]
  | Tuple (l, _) -> List.fold_left (fun a b -> a @ get_all_ids b) [] l
  | Constructor(_, Some expr, _) -> get_all_ids expr
  | FixedType (t, _, _) -> get_all_ids t
  | _ -> []

(* unify a b will try to unify b with a, and if a match with b will change the environment according to the modification needed in a for havigng a = b*)
let rec unify ident expr env error_infos = 
  (*let _ = Printf.printf "unyfing %s with %s\n" (print_value expr ) (pretty_print ident) in*)
  match (ident, expr) with
  | FixedType (t, _, _), t' -> unify t t' env error_infos
  | Const a, FInt b when a = b -> env
  | Underscore, _ -> env
  | Unit, FUnit -> env
  | Bool a, FBool b when a = b -> env
  | Ident (ident, _), _ -> Env.add env ident expr
  | Constructor(name, None, er), FConstructor(name', None) ->
    if snd name = snd name' then
      env
    else
      raise (send_error (Printf.sprintf "Can't unify constructors %s with %s" (string_of_ident name) (string_of_ident name')) er)
  | Constructor(name, Some expr, er), FConstructor(name', Some expr')  ->
    if snd name = snd name' then
      unify expr expr' env er
    else
      raise (send_error (Printf.sprintf "Can't unify constructors %s with %s" (string_of_ident name) (string_of_ident name')) er)
  | Tuple (l1, error), FTuple l2 ->
    if tuple_has_double_id ident then
      raise (send_error "variable bounded several times in tuple" error)
    else
      let rec aux l1 l2 env =  begin match  (l1, l2) with
        | [], [] -> env
        | x1::t1, x2::t2 -> unify x1 x2 (aux t1 t2 env) error
        | _ -> raise (send_error (Printf.sprintf "Can't unify %s with %s" (print_value expr) (pretty_print_aux ident "" true)) error_infos )
      end in aux l1 l2 env
  | _ -> raise (send_error (Printf.sprintf "Can't unify %s with %s" (pretty_print_aux ident "" true) (print_value expr)) error_infos )



(* interpret a program. It uses closures, because it is very easy to implement exceptions with them *)
let interpret program env k kE = 
  let env_t = ref env in
  let rec aux env k kE program =
    match program with
    | Underscore  -> k FUnit env
    | FixedType (x, _, _) -> let k' x' _ = k x' env in aux env k' kE x
    | Const x -> k (FInt x) env
    | Value x -> k x env
    | Bool x -> k (FBool x) env
    (*| RefValue (x) -> k program  env
   *) | Constructor(name, None, er) -> k (FConstructor (name, None)) env 
   (* | Array _ -> k program env
    | Closure _ -> k program env
    | BuildinClosure _ -> k program env
    | ClosureRec _ -> k program env
   *) | Ident ( name, error_infos)  -> 
      let o = try
          Env.get_most_recent env name
        with Not_found ->
          raise  ((send_error ("Identifier '"^ string_of_ident name ^"' not found") error_infos))
      in k o env
    | Tuple (l, error_infos) ->
      let rec aux_tuple acc l = begin match l with
        | [] -> k (FTuple (List.rev acc)) env
        | x::tl -> let k' x' _ =
                     aux_tuple (x'::acc) tl
          in aux env k' kE x
      end in aux_tuple [] l
    | TypeDecl(id, l, error_infos) -> 
      (*let res, env = interpret_type_declaration id l error_infos env
        in let _ = env_t := env
        in k res env*)
      k FUnit env
    | Constructor(name, Some expr, error_infos) ->
      let k' x' _ =
        (* if Env.mem_type env name then *)
        k (FConstructor(name, Some x')) env
        (*else
          raise (send_error (Printf.sprintf "Constructor %s not defined" name) error_infos)*)
      in aux env k' kE expr
    | Unit -> k FUnit env
    | Bang (x, error_infos) ->
      let k' x' _ = 
        begin
          match x' with
          | FRef y -> k !y env
          | _ -> raise (send_error "Can't deref a non ref value" error_infos)
        end 
      in aux env k' kE x
    | Ref (x, error_infos) ->
      let k' x' _ =
        k (FRef (ref x')) env
      in aux env k' kE x
    | Not (x, error_infos) -> 
      let k' x' _ =
        begin 
          match x' with
          | FBool y -> k (FBool (not y)) env
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
        | FixedType(Ident (name, _), _, _)
        | Ident (name, _) ->
          begin match b with
            | Fun (id, expr, _) -> 
              let clos = (FClosureRec(name, id, expr, env)) (*recursive closure are here to allow us to add the binding of id with expr at the last moment *)
              in let _ = env_t := (Env.add env name clos )
              in k clos !env_t
            | _ -> let k' b' _ = 
                     let _ = env_t := (unify a b' env error_infos)
                     in k b' !env_t
              in aux env k' kE b
          end

        | _ -> raise (send_error "a function declaration must begin by an id" error_infos)
      end


    | In(_, Let(_), error_infos) -> raise (send_error "An 'in' clause can't end with a let. It must returns something" error_infos)
    | MainSeq(a, b, error_infos) | Seq(a, b, error_infos) ->
      let k' a' env' = 
        aux env' k kE b (* why ref? just because we need the secondone to be a copy of the env of the firstone *)
      in aux env k' kE a
    | In (a, b, error_infos) -> 
      begin match a with
        | LetRec (FixedType(Ident (name, _), _, _), Fun (arg, expr, _), _) 
        | LetRec (Ident (name, _), Fun (arg, expr, _), _) ->
          let clos = (FClosureRec(name, arg, expr, env))
          in aux (Env.add env name clos) k kE b
        | Let (a, expr, error_infos) -> 
          let k' expr' _ = 
            aux (unify a expr' env error_infos) k kE b
          in aux env k' kE expr
        | _ -> raise (send_error "incorrect in" error_infos)
      end

    | Fun (id, expr, error_infos) -> 
      k (FClosure(id, expr, env)) env
    | IfThenElse(cond, a, b, error_infos) ->
      let k' cond' _ = 
        begin 
          match (cond') with
          | FBool false -> aux env k kE b
          | FBool true -> aux env k kE a
          | _ -> raise (send_error "In a If clause the condition must return a boolean" error_infos)
        end
      in aux env k' kE cond
    | Call(fct, arg, error_infos) -> 
      let k'' arg' _ =
        let k' fct' _ =
          begin match (fct') with 
            | FConstructor (name, None) ->
              k (FConstructor(name, Some arg'))  env
            | FBuildin (fct) ->
              k (fct arg') env
            | FClosure (key, expr, env_fct) ->
              aux (unify key arg' env_fct error_infos) k kE expr
            | FClosureRec(key, arg_key, expr, env_fct) ->
              let env_fct = Env.add env_fct key fct'
              in let env_fct = unify arg_key arg' env_fct error_infos
              in aux env_fct k kE expr
            | _ -> raise (send_error "You are probably calling a function with too much parameters " error_infos)

          end
        in aux env k' kE fct
      in aux env k'' kE arg
    | Printin(expr, error_infos) -> 
      let k' a _ = 
        begin
          match a with
          | FInt x ->  let _ = Printf.printf "%d\n" x in k (FInt(x)) env
          | _ -> raise (send_error "This function is called 'prInt'. How could it work on non-integer values" error_infos)
        end 
      in aux env k' kE expr 
    | Raise (e, error_infos) ->
      aux env kE kE e
    (* we have two try with syntaxes: one with matching, the other without *)
    | TryWith (t_exp, Ident (x, _), w_exp, error_infos) ->
      let kE' t_exp' _ =
        aux (Env.add env x t_exp')  k kE w_exp 
      in aux env k kE' t_exp
    | TryWith (t_exp, Const(er), w_exp, error_infos) ->
      let kE' t_exp' _ =
        match (t_exp') with
        | FInt(v) when v = er -> aux env k kE w_exp 
        | _ -> aux env k kE t_exp
      in aux env k kE' t_exp

    | ArrayMake (expr, error_infos) ->
      let k' a _ = 
        begin
          match a with
          | FInt x when x < 0 -> raise (send_error (Printf.sprintf "The size (%d) of this array will be negative" x) error_infos)
          | FInt x -> k (FArray (Array.make x 0)) env
          | _ -> raise (send_error "An array must have an integer size" error_infos)
        end 
      in aux env k' kE expr

    | ArrayItem (id, expr, error_infos) ->
      let k'' id' _ =
        let k' expr' _ = 
          begin match (id', expr') with
            | FArray (x), FInt (i) -> 
              if i < 0 || i >= Array.length x then
                raise (send_error ((Printf.sprintf "You are accessing element %d of an array of size %d") i (Array.length x)) error_infos)
              else 
                k (FInt x.(i)) env
            | a, b -> raise (send_error ("Bad way to access an array") error_infos)
          end 
        in aux env k' kE expr
      in aux env k'' kE id


    | ArraySet (id, expr, nvalue, error_infos) ->
      let k_value nvalue' _ = 
        let k'' id' _ =
          let k' expr' _ = 
            begin match (id', expr', nvalue') with
              | FArray (x), FInt (i), FInt(y) -> (* pensez à ajouter la generation d'exceptions aprés coup *)
                if i < 0 || i >= Array.length x then
                  raise (send_error ((Printf.sprintf "You are accessing element %d of an array of size %d") i (Array.length x)) error_infos)
                else 
                  x.(i) <- y; k FUnit env
              | _ -> raise (send_error "When seting the element of an array, the left side must be an array, the indices an integer and the value an integer" error_infos)
            end 
          in aux env k' kE expr
        in aux env k'' kE id
      in aux env k_value kE nvalue

    | MatchWith (expr, match_list, error ) ->
      let k' expr' _ = 
        let rec aux_match l =
          let _ = if l <> [] then Printf.printf "trying mathc with %s\n" (pretty_print @@ fst @@ List.hd l) in
          match l with
          | (pattern, action)::tl ->
            begin
              try
                let env' = unify pattern expr' env error
                in aux env' k kE action
              with InterpretationError m ->
                let _ = Printf.printf "[[[[[[[[[[[[[[[[[[%s]]]]]]]]]]]]]]]]]]" m in
                aux_match tl
            end
          | [] -> raise (send_error (Printf.sprintf "Didn't match the expr : %s" (print_value expr')) error)
        in aux_match match_list

      in aux env k' kE expr

    | Module (name, content, _, error_infos) ->
      k FUnit env

    | _ -> raise (send_error "You encountered something we can't interpret. Sorry" (Lexing.dummy_pos))

  in let e,x = aux env k kE program
  in e, !env_t

