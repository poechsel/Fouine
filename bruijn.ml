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
    | Tuple (l, ld) ->
        let _, l' = process_tuple [] l d
        in Tuple (l', ld)
    | In (Let (Ident (id, _), Tuple (l2, _), _), expr, ld) ->
        let l1', l2' = process_tuple [] l2 d 
        in let _ = Dream.add d (string_of_ident id) in LetIn (Tuple (l2', ld), aux d expr) 
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
        Access (Dream.naming d (string_of_ident x))
        (*if DreamEnv.is_builtin x
          then Bclosure x
        else Access (Dream.naming d x)
            *)
    | Fun ((Ident (x, _)), e', _) -> 
        let d' = Dream.copy d in
        begin
          Dream.add d' (string_of_ident x);
          Lambda (aux d' e')
        end
    | Fun (_, e, _) -> Lambda (aux d e)
    | Let ((Ident (x, _)), a, ld) -> 
        let new_a = aux d a in
        let _ = Dream.add d (string_of_ident x) 
        in Let (new_a, Unit, ld) (* on rajoute x au scope global qui suit (d est un référence vers l'environnement) *)
    | LetRec ((Ident(f, _)), Fun ((Ident(x, _)), a, _), ld) ->
          let d' = Dream.copy d in
          let new_a = 
            (begin
              Dream.add d' (string_of_ident f);
              Dream.add d' (string_of_ident x);
              aux d' a
            end) 
          in begin
               Dream.add d (string_of_ident f);
               Let (LambdaR (new_a), Unit, ld)
             end
    | LetRec ((Ident(f, _)), a, ld) ->
        begin
          Dream.add d (string_of_ident f);
          Let (aux d a, Unit, ld)
        end
    | Let (Underscore, expr, ld) -> (aux d expr) 
    | In (Let ((Ident(x, _)), expr, _), expr', _) ->
        let d' = Dream.copy d in
        let d'' = Dream.copy d in
        let new_expr = aux d' expr in
        begin
          Dream.add d'' (string_of_ident x);
          LetIn (new_expr, aux d'' expr')
        end
    | In (Let (Underscore, expr, _), expr', ld) -> aux d (MainSeq (expr, expr', ld)) 
    | In (LetRec ((Ident(f, _)), Fun ((Ident(x, _)), a, _), _), b, _) ->
        let d' = Dream.copy d in
        begin
          Dream.add d (string_of_ident f);
          Dream.add d (string_of_ident x);
          let new_a = aux d a in 
          begin
            Dream.add d' (string_of_ident f);
            LetIn (LambdaR (new_a), aux d' b)
          end
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
    | TryWith (a, (Ident(x, _)), b, ld) -> 
        let d' = Dream.copy d in
        begin
          Dream.add d' (string_of_ident x);
          TryWith (aux d a, Unit, aux d' b, ld)
        end
    | Printin (a, ld) -> Printin (aux d a, ld)
    | Raise (a, ld) -> Raise (aux d a, ld)
    | _ -> e 


and process_tuple l1 l2 d =
  let f d a = let d' = Dream.copy d in aux d' a
  and g d x = match x with
        | Ident (id, _) -> Dream.add d (string_of_ident id); x
        | x -> x
  in let l2' = List.map (f d) l2
  in let l1' = List.map (g d) l1 (* on laisse le traitement physique de l2 à compilB, et on se contente de ramasser les noms de nouvelles variables pour le reste du programme *)
  in l1', l2'


in aux (Dream.init ()) e

