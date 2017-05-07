(* lib to convert names of access operations to De Bruijn indices *)
open Dream
open Expr

let bruijn_debug d e = 
  begin
    print_endline @@ Printf.sprintf "There are %s vars binded." (string_of_int (Dream.size d));
    print_endline @@ Printf.sprintf "Their names are : %s" (Array.fold_left (fun a b -> a ^ b ^ " ") "" (Dream.get_mem d));
    print_endline @@ Printf.sprintf "Now processing expression %s" (show_expr e)
  end
  

let convert_bruijn e debug =
  let rec aux d e =
    begin if debug then bruijn_debug d e else () end;
    match e with
    | Let (Ident (id, _), Tuple (l2, _), ld) ->
        let l1', l2' = process_tuple [] l2 d 
        in let _ = Dream.add d id in Let (Tuple (l2', ld), Unit, ld)
    | In (Let (Ident (id, _), Tuple (l2, _), _), expr, ld) ->
        let l1', l2' = process_tuple [] l2 d 
        in let _ = Dream.add d id in LetIn (Tuple (l2', ld), aux d expr) 
    | In (Let (Tuple (l1, _), Ident (id, _), _), expr, ld) ->
        let access_id = aux d (Ident (id, ld)) in
        let l1', l2' = process_tuple l1 [] d in
        LetInTup (Tuple (l1', ld), access_id, aux d expr)
    | Let (Tuple (l1, _), Tuple (l2, _), ld) ->
        let l1', l2' = process_tuple l1 l2 d 
        in LetTup (Tuple (l1', ld), Tuple (l2', ld))
    | In(Let(Tuple (l1, _), Tuple (l2, _), _), expr, ld) ->
        let l1', l2' = process_tuple l1 l2 d
        in LetInTup (Tuple (l1', ld), Tuple (l2', ld), aux d expr)
    | Ident (x, _) ->
        Access (Dream.naming d x)
        (*if DreamEnv.is_builtin x
          then Bclosure x
        else Access (Dream.naming d x)
            *)
    | Fun (Underscore, e, _) -> Lambda (aux d e)
    | Fun (Unit, e, _) -> Lambda (aux d e)
    | Fun (Ident(x, _), e', _) -> 
        let d' = Dream.copy d in
        begin
          Dream.add d' x;
          Lambda (aux d' e')
        end
    | Let (Ident (x, _), a, ld) -> 
        let new_a = aux d a in
        let _ = Dream.add d x in Let (new_a, Unit, ld) (* on rajoute x au scope global qui suit (d est un référence vers l'environnement) *)
    | LetRec (Ident (f, _), Fun (Ident (x, _), a, _), ld) ->
          let d' = Dream.copy d in
          let new_a = 
          (begin
            Dream.add d' f;
            Dream.add d' x;
            aux d' a
          end) in
            begin
              Dream.add d f;
              Let (LambdaR (new_a), Unit, ld)
            end
    | LetRec (Ident (f, _), a, ld) ->
        begin
          Dream.add d f;
          Let (aux d a, Unit, ld)
        end
    | Let (Underscore, expr, ld) -> (aux d expr) 
    | In (Let (Ident(x, _), expr, _), expr', _) ->
        let d' = Dream.copy d in
        let d'' = Dream.copy d in
        let new_expr = aux d' expr in
        begin
          Dream.add d'' x;
          LetIn (new_expr, aux d'' expr')
        end
    | In (Let (Underscore, expr, _), expr', ld) -> aux d (MainSeq (expr, expr', ld)) 
    | In (LetRec (Ident (f, _), Fun (Ident (x, _), a, _), _), b, _) ->
        let d' = Dream.copy d in
        begin
          Dream.add d f;
          Dream.add d x;
          let new_a = aux d a in 
          begin
            Dream.add d' f;
            LetIn (LambdaR (new_a), aux d' b)
          end
        end
   (* | LetRec (Ident (f, _), Fun (Ident (x, _), a, _), _) ->
        begin
          Dream.add d f;
          Dream.add d x;
          Let (LambdaR (aux d a), Unit, Lexing.dummy_pos)
        end *)
    | BinOp (op, e1, e2, ld) ->
        let d' = Dream.copy d in
        BinOp (op, aux d e1, aux d' e2, ld)
   (* | Call (Ident ("prInt", _), a, ld *)
    | Call (a, b, ld) ->
        let d' = Dream.copy d in
        let new_a = aux d a in
        Call (new_a, aux d' b, ld)
    | IfThenElse (cond, a, b, ld) ->
        let d' = Dream.copy d in
        let d'' = Dream.copy d in
        IfThenElse (aux d cond, aux d' a, aux d'' b, ld)
    | Seq (a, b, ld) | MainSeq (a, b, ld) | In (a, b, ld) ->
        let new_a = aux d a in
        MainSeq (new_a, aux d b, ld)
    | Bang (a, ld) -> Bang (aux d a, ld)
    | ArraySet (a, i, new_value, ld) ->
        let d' = Dream.copy d in
        let d'' = Dream.copy d in
        ArraySet (aux d a, aux d' i, aux d'' new_value, ld)
    | ArrayMake (a, ld) -> ArrayMake (aux d a, ld)
    | ArrayItem (x, y, ld) -> 
        let d' = Dream.copy d in
        ArrayItem (aux d x, aux d' y, ld)
    | TryWith (a, Const (k), b, ld) ->
        let d' = Dream.copy d in
        TryWith (aux d a, Const k, aux d' b, ld)
    | TryWith (a, Ident (x, _), b, ld) -> 
        let d' = Dream.copy d in
        begin
          Dream.add d' x;
          TryWith (aux d a, Unit, aux d' b, ld)
        end
    | Printin (a, ld) -> Printin (aux d a, ld)
    | Raise (a, ld) -> Raise (aux d a, ld)
    | _ -> e 

and process_tuple l1 l2 d =
  let f d a = let d' = Dream.copy d in aux d' a
  and g d x = match x with
        | Ident (id, _) -> Dream.add d id; x
        | x -> x
  in let l2' = List.map (f d) l2
  in let l1' = List.map (g d) l1 (* on laisse le traitement physique de l2 à compilB, et on se contente de ramasser les noms de nouvelles variables pour le reste du programme *)
  in l1', l2'


in aux (Dream.init ()) e

(* old tests, useless to compile

type test = | Cls of string*test 
            | Unitcls of test 
            | Expr of (test list) 
            | Op 
            | AccS of string 
            | Prod of test*test
            | Acc of int

let convert_test e =
  let rec aux d e =
    match e with
    | AccS x -> Acc (Dream.naming d x)
    | Cls (x, e') -> begin
                          Dream.add d x;
                          Unitcls (aux d e')
                        end
    | Expr l -> Expr (convert_list d l)
    | Prod (a, b) -> let d' = Dream.copy d in Prod (aux d a, aux d' b)
    | Unitcls e' -> Unitcls (aux d e')
    | Op -> Op
    | _ -> failwith "bad case"
  
  and convert_list d = function
    | [] -> []
    | h :: t -> (aux (Dream.copy d) h) :: (convert_list d t)

  in aux (Dream.init ()) e

(* the K combinator *)
let t1 = Cls ("x", Cls ("y", AccS "x"))

(* the S combinator *)
let t2 = Cls("x", Cls("y", Cls("z", Expr [AccS "x"; AccS "z"; Prod (AccS "y", AccS "z")])))

let t3 = Cls ("z", Prod (Cls ("y", Prod (AccS "y", Cls ("x", AccS "x"))), Cls ("x", Prod (AccS "z", AccS "x"))))

(*
let rec nameless e =
  match e with
  | NamedCls (x, t) -> Cls (nameless t)
  | Expr l -> Expr (List.map nameless l)
  | _ -> e
*)

(* translation to De Bruijn terms *)

(* useless for now
let rec s e b n =
  begin
  match e with
  | Prod (a, c) -> Prod (s a b n, s c b n)
  | Cls a -> Cls (s a b (n+1))
  | Acc m -> if m > n + 1 then Acc (m-1)
             else if m = n + 1 then t 0 n b
             else Acc m
  end

and t i n e =
  begin
  match e with
  | Prod (a, b) -> Prod (t i n a, t i n b)
  | Cls a -> Cls (t (i+1) n a)
  | Acc m -> if m > i then Acc (m + n)
             else Acc m
  end
*)
*)
