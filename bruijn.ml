(* lib to convert names of access operations to De Bruijn indices *)
open Dream
open Expr

type test = | Cls of string*test 
            | Unitcls of test 
            | Expr of (test list) 
            | Op 
            | AccS of string 
            | Prod of test*test
            | Acc of int

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
let convert e =
  let rec aux d e =
    begin
    match e with
    | Ident (x, _) -> Access (Dream.naming d x)
    | Fun (Ident(x, _), e', _) -> 
        begin
          Dream.add d x;
          Lambda (aux d e')
        end
    | In (Let (Ident(x, _), expr, _), expr', _) ->
        let d' = Dream.copy d in
        let new_expr = aux d expr in
          begin
            Dream.add d' x;
            LetIn (new_expr, aux d' expr')
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
    | _ -> e
    end
  in aux (Dream.init ()) e


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
