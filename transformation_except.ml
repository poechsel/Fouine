open Env
open Prettyprint
open Expr

let p = Lexing.dummy_pos
let k = Ident(".k", p)
let kE = Ident(".kE", p)
let create_wrapper content = Fun(k, Fun(kE, content, p), p)

let y = Ident("buildins_y", p)


(* rename all occurence of a name inside a recursive function *)
let rec rename_in_rec target_name name program = 
  let rename = rename_in_rec target_name name in
  match program with
  | Ident (x, er) when x = target_name -> Ident(name, er)
  | Tuple (l, er) -> Tuple (List.map rename l, er)
  | Constructor(name, expr, er) -> Constructor(name, rename expr, er)
  | Bang(x, er) -> Bang(rename x, er)
  | Ref (x, er) -> Ref(rename x, er)
  | Not (x, er) -> Ref(rename x, er)
  | BinOp (x, a, b, er) -> BinOp(x, rename a, rename b, er)
  | Let (a, b, er) -> Let (rename a, rename b, er)
  | LetRec(a, b, er) -> LetRec (rename a, rename b, er)
  | In(a, x, er) -> In(rename a, rename x, er)
  | Fun(x, expr, er) -> Fun(rename x, rename expr, er)
  | IfThenElse(cond, a, b, er) -> IfThenElse (rename cond, rename a, rename b, er)
  | Call(fct, arg, er) -> Call(rename fct, rename arg, er)
  | Printin(expr, er) -> Printin (rename expr, er)
  | Raise (e, er) -> Raise (rename e, er)
  | TryWith(t, m, w, er) -> TryWith (rename t, rename m, rename w, er)
  | ArrayMake (x, er) -> ArrayMake(rename x, er)
  | ArrayItem(id, expr, er) -> ArrayItem(rename id, rename expr, er)
  | ArraySet(a, b, c, er) -> ArraySet(rename a, rename b, rename c, er)
  | MatchWith(expr, match_list, er) ->
    MatchWith(rename expr, List.map (fun (a, b) -> (rename a, rename b)) match_list, er)
  | ClosureRec(a, b, c, env) -> ClosureRec(a, rename b, rename c, env)
  | Closure(a, b, env) -> Closure(rename a, rename b, env)
  | Seq(a, b, er) -> Seq(rename a, rename b, er)
  | MainSeq(a, b, er) -> MainSeq(rename a, rename b, er)

  | _ -> program

 



let transform_exceptions code =
  let rec aux code =
    match code with 
    | Const _ -> create_wrapper (Call(k, code, p))
    | Bool _ -> create_wrapper (Call(k, code, p))

    | Ident (x, er) -> create_wrapper (Call( k, Ident (x, er), p))
    | Array _ -> create_wrapper (Call( k, code, p))
    | Underscore -> create_wrapper (Call(k, code, p))
    | Unit -> create_wrapper (Call(k, code, p))
    | Constructor_noarg _ -> create_wrapper (Call(k, code, p))

    | Tuple (l, er) ->
      begin
        let rec create_vars l i = 
          match l with
          | [] -> []
          | x::t -> Ident(".t_" ^ string_of_int i, p) :: create_vars t (i+1)
        in let vars = create_vars l 0
        in let out = Call(k, Tuple (List.fold_left (fun a b -> b :: a) [] (List.rev vars) , er), p)
        in let f = List.fold_right (fun (expr, var) b -> 
            Call(Call(aux expr, Fun(var, b, p), p), kE, p))

        (List.combine l vars) out
          
        in create_wrapper f
          end

    | Constructor(name, expr, er) ->
      create_wrapper @@
      Call(Call(aux expr,
                Fun(Ident(".e", p), Call(k, Constructor(name, Ident(".e", p), er), p), p)
                  , p), kE, p)
    | Let(x, e1, _) ->
      create_wrapper @@
      Let (x, aux e1,p)
           
    | In(Let(x, e1, _), e2, _) ->
      create_wrapper @@
      Call(Call(aux e1,
                Fun(x, Call(Call(aux e2, k, p), kE, p), p), p), kE, p)


    | MatchWith (expr, pattern_actions, err) ->
        create_wrapper @@
        Call(Call(aux expr, 
            Fun(Ident(".expr", p),
           MatchWith(expr, 
                         List.map (fun (pattern, action) -> (pattern,  Call(Call(aux (Ident(".expr", p)), Fun(pattern, Call(Call(aux action, k, p), kE, p), p), p), kE, p)))
                          pattern_actions, err), p)
              
                 
                 , p), kE, p)


    | Raise (expr, er) ->
      create_wrapper @@
      Call(Call(aux expr, kE, er), kE, er)
    | TryWith (tr, pattern, expr, er) ->
      create_wrapper @@
      Call(Call(aux tr, k, p), Fun(pattern, 
                Call(Call(aux expr, k, p), kE, p), p), p)

    | IfThenElse(cond, a, b, er) ->
        create_wrapper @@
        Call(Call(aux cond,
                  Fun(Ident(".cond", p), 
                      IfThenElse(Ident(".cond", p), 
                                 Call(Call(aux a, k, p), kE, p),
                                Call(Call(aux b, k, p), kE, p),er), p)
                 , p),
               kE, p)
    | BinOp(x, a, b, er) ->
      create_wrapper @@
      Call(Call(aux a,
           (Fun(Ident(".a", p), 
                Call(Call(aux b,
                     Fun (Ident(".b", p), Call(k, BinOp(x, Ident(".a", p), Ident(".b", p), er), p), p), p) , kE, p), p)), p), kE, p)
    | Fun(x, expr, er) ->
      create_wrapper @@
        Call(k, (Fun(x, aux expr, er)), p)
    | Call(Constructor_noarg(name, b), arg, er ) ->
      aux (Constructor(name, arg, b))
    | Call(x, e, er) ->
      create_wrapper @@
      Call(Call(aux e,
           (Fun(Ident(".v2", p), 
                Call(Call(aux x,
                     Fun (Ident(".f", p), 
                          Call(Call(Call(Ident(".f", p), Ident(".v2", p), p), k, p), 
                               kE, p), p), p)
                    , kE, p), p)), p)
          , kE, p)
    | In(LetRec(x, e1, _), e2, _) ->
      match x with
      | Ident(name, er) ->
(*let fact = let fact t_fact = fun n ->   if n = 0 then     1   else     n * (t_fact (n - 1)) in buildins_y fact in fact 8*)

    let code = 
   (* In(Let(
         y,
         Fun(Ident("t", p),
             In(Let(Ident("p", p),
                    Fun(Ident("f", p),
                        Fun(Ident("x", p),
                            Call(Call(Ident("t", p),
                                      Call(Ident("t", p), Ident("t", p), p), p),
                                 Ident("x", p), p),
                            p),
                        p),
                    p),
                Call(Ident("p", p), Ident("p", p), p), p), p), p),
*)
      In(Let(x,
             In(Let(
                 x,
                 Fun(Ident("t_" ^ name, p), 
                     rename_in_rec name ("t_" ^ name) e1, p), p),
                Call(y, x, p)
               ,p), p
            ), e2, p)
  (*      ,p) *)
        (*let code = (In(
            Let(x, 
                In(Let(x, Fun(Ident("t_"^name, p), p),
                                        rename_in_rec name ("t_" ^ name) e1
                    , p), 
                   Call(y, Ident("t_"^name, p), p)
                  , p)
               ,p)
          , e2, p)) *)
in

        let _ = Printf.printf ("==================== \n%s\n=================\n") @@ pretty_print @@
code in
        aux   code
    | Printin(expr, er) ->
      create_wrapper @@
      Call(Call(aux expr,
                Fun(Ident(".e", p), Call(k, Printin(Ident(".e", p), p), er), p)
                  , p), kE, p)
    | ArrayMake(expr, er) ->
      create_wrapper @@
      Call(Call(aux expr,
                Fun(Ident(".e", p), Call(k, ArrayMake(Ident(".e", p), er), p), p)
                  , p), kE, p)
    | Not(expr, er) ->
      create_wrapper @@
      Call(Call(aux expr,
                Fun(Ident(".e", p), Call(k, Not(Ident(".e", p), er), p), p)
                  , p), kE, p)

    | ArrayItem(ar, index, er) ->
      create_wrapper @@
      Call(Call(aux ar,
                Fun(Ident(".ar", p),
                    Call(Call(aux index,
                              Fun(Ident(".index", p),
                                  Call(k, ArrayItem(Ident(".ar", p), Ident(".index", p), er), p),
                                 p), p), kE, p), p), p), kE, p)
    | ArraySet(ar, index, what, er) ->
      create_wrapper @@
      Call(Call(aux ar,
                Fun(Ident(".ar", p),
                    Call(Call(aux index,
                              Fun(Ident(".index", p),
                                  Call(Call(aux what, 
                                            Fun(Ident(".what", p),
                                  Call(k, ArraySet(Ident(".ar", p), Ident(".index", p), Ident(".what", p), er), p),
                                 p), p), kE, p), p), p), kE, p), p), p), kE, p)
    | Bang(expr, er) ->
      create_wrapper @@
      Call(Call(aux expr,
                Fun(Ident(".e", p), Call(k, Bang(Ident(".e", p), er), p), p)
                  , p), kE, p)
    | Ref(expr, er) ->
      create_wrapper @@
      Call(Call(aux expr,
                Fun(Ident(".e", p), Call(k, Ref(Ident(".e", p), er), p), p)
                  , p), kE, p)

    | Seq(expr1, expr2, er) | MainSeq(expr1, expr2, er) ->
      create_wrapper @@
      Call(Call(aux expr1, 
               Fun(Underscore, Call(Call(aux expr2, k, p), kE, p), p), p), kE, p)
    | In(_, _, _) -> failwith "error"

  in let x = Ident(".x", p)
  in match code with
  | TypeDecl _ -> code
  | _ ->     Call(Call(aux code, Fun(x, x, p), p), Fun(x, x, p), p)


