(* lib to convert names of access operations to De Bruijn indices *)
open Dream
open Expr

let convert e =
  let rec aux d e =
    begin
      print_endline @@ string_of_int (Dream.size d);
      print_endline @@ (Array.fold_left (fun a b -> a ^ b ^ " ") "" d.arr);
      print_endline @@ (show_expr e);
    begin
    match e with
    | Tuple _ -> failwith "tuple"
    | Ident (x, _) -> Access (Dream.naming d x)
    | Fun (Ident(x, _), e', _) -> 
        let d' = Dream.copy d in
        begin
          Dream.add d' x;
          Lambda (aux d' e')
        end
    | Let (Ident (x, _), a, ld) ->
        begin
          Dream.add d x;
          Let (aux d a, Unit, ld)
        end
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
   (* | In (Let (Underscore, expr, _), expr', _) ->
      let d' = Dream.copy d in
      let d'' = Dream.copy d in
      let new_expr = aux d' expr in
        MainSeq (new_expr, aux d'' expr', Lexing.dummy_pos) *)
    | In (Let (Ident(x, _), expr, _), expr', _) ->
      let d' = Dream.copy d in
      let d'' = Dream.copy d in
      let new_expr = aux d' expr in
      begin
        Dream.add d'' x;
        LetIn (new_expr, aux d'' expr')
      end
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
    | LetRec (Ident (f, _), Fun (Ident (x, _), a, _), _) ->
        begin
          Dream.add d f;
          Dream.add d x;
          Let (LambdaR (aux d a), Unit, Lexing.dummy_pos)
        end
    | BinOp (op, e1, e2, ld) ->
        let d' = Dream.copy d in
        BinOp (op, aux d e1, aux d' e2, ld)
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
    end
  end
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
