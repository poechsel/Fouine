open Env
open Prettyprint
open Expr

let p = Lexing.dummy_pos
let k = Ident(".k", p)
let kE = Ident(".kE", p)
let create_wrapper content = Fun(k, Fun(kE, content, p), p)

let transform_exceptions code =
  let rec aux code =
    match code with 
    | Const _ -> create_wrapper (Call(k, code, p))
    | Bool _ -> create_wrapper (Call(k, code, p))

    | Ident (x, er) -> create_wrapper (Call( k, Ident (x, er), p))
    | Array _ -> create_wrapper (Call( k, code, p))

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
  (*  | In(LetRec(x, e1, _), e2, _) ->
      create_wrapper @@
      In(LetRec(x, create_wrapper @@ aux e1, p)
      create_wrapper @@
      Call(Call(aux e1,
                Fun(Ident(".x", p), 
                    In(LetRec(x, Ident(".x", p), p),
                       Call(Call(aux e2, k, p), kE, p), p), p), p), kE, p)
   *) | In(Let(x, e1, _), e2, _) ->
      create_wrapper @@
      Call(Call(aux e1,
                Fun(x, Call(Call(aux e2, k, p), kE, p), p), p), kE, p)

    | Printin(expr, er) ->
      create_wrapper @@
      Call(Call(aux expr,
                Fun(Ident(".e", p), Printin(Ident(".e", p), er), p)
                  , p), kE, p)
    | ArrayMake(expr, er) ->
      create_wrapper @@
      Call(Call(aux expr,
                Fun(Ident(".e", p), ArrayMake(Ident(".e", p), er), p)
                  , p), kE, p)

  in let x = Ident(".x", p)
  in Call(Call(aux code, Fun(x, x, p), p), Fun(x, x, p), p)


