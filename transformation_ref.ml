open Env
open Prettyprint
open Expr

let p = Lexing.dummy_pos
let memory_name = Ident("_memory", p)


let allocate = Fun(Ident("_v", p), Fun(Ident("_s1", p), Tuple([Ref(Ident("_v", p), p); Ident("_s1", p)], p), p), p)
let read = Fun(Ident("_v", p), Fun(Ident("_s1", p), Bang(Ident("_v", p), p), p), p)
let modify =Fun(Ident("_s2", p), Fun(Tuple([Ident("_l1", p); Ident("_v2", p)], p), 
                                     Seq(BinOp(refSet, Ident("_l1", p), Ident("_v2", p), p), Ident("_s2", p), p), p),p)

(* refs will be representend by a const equivalent to a pointer. We use inference to make sure that the typing is correct *)
let rec transform_ref code =
  let rec aux code = 
    match code with
    | Const _ -> Fun(memory_name, Tuple([code; memory_name], p), p)
    | Bool _ -> Fun(memory_name, Tuple([code; memory_name], p), p)
    | Unit -> Fun(memory_name, Tuple([code; memory_name], p), p)
    | Underscore -> Fun(memory_name, Tuple([code; memory_name], p), p)
    | Tuple _ -> Fun(memory_name, Tuple([code; memory_name], p), p)
    | Ident _ -> Fun(memory_name, Tuple([code; memory_name], p), p)
    | RefValue _ -> Fun(memory_name, Tuple([code; memory_name], p), p)
    | Array _ -> Fun(memory_name, Tuple([code; memory_name], p), p)

    | BinOp(x, a, b, er) when x#symbol = ":=" -> 
      Fun (memory_name,
           In(Let(Tuple([Ident("_l1", p); Ident("_s1", p)], p),
                  Call(aux a, memory_name, p), p),
             In(Let(Tuple([Ident("_v2", p); Ident("_s2", p)], p),
                    Call(aux b, Ident("_s1", p), p), p),
                In(Let(Ident("_s3", p), 
                       Call(Call(modify,
                                 Ident("_s2", p), p),
                            Tuple([Ident("_l1", p); Ident("_v2", p)], p), p)
                      , p),
                   Tuple([Ident("_v2", p); Ident("_s3", p)], p), p),p),p),p)

    | BinOp(x, a, b, er) ->
      Fun(memory_name, 
          In(Let(Tuple([Ident("_f1", p); Ident("_s1", p)], p), Call(aux a, memory_name, p), p),
             In( Let(Tuple([Ident("_f2", p); Ident("_s2", p)], p), Call(aux b, Ident("_s1", p), p), p),
                 Tuple([BinOp(x, Ident("_f1", p), Ident("_f2", p), er); Ident("_s2", p)], p), p), p ), p)
    | Let(a, b, er) ->
      Fun(memory_name, 
          In(Let (Tuple([Ident("_x1", p); Ident("_s1", p)], p), Call(aux b, memory_name, p), p),
             In(Let(a, Ident("_x1", p), er), Tuple([a; Ident("_s1", p)], p), p)
            ,p), p)
    | In(Let(a, b, er), expr, _) ->
      Fun(memory_name, 
          In(Let (Tuple([Ident("_x1", p); Ident("_s1", p)], p), Call(aux b, memory_name, p), p),
             In(Let(a, Ident("_x1", p), er), Call(aux expr, Ident("_s1", p), p), p)
            ,p), p)
    | LetRec(a, Fun(arg, e, _), er) ->
    Fun(memory_name, 
        In(LetRec(a, Fun(arg, aux e, p), p),
           Tuple([a; memory_name], p)
       , p), p)
    | In(LetRec(a, Fun(arg, e, _), er), expr, _) ->
    Fun(memory_name, 
        In(LetRec(a, Fun(arg, aux e, p), p),
           Call(aux expr, memory_name, p)
             , p),p
       )


    | Ref (x, error_infos) -> 
      Fun(memory_name,
          In(Let(Tuple([Ident("_v", p); Ident("_s1", p)], p)
                , Call(aux x, memory_name, p),p), 
             In(Let(Tuple([Ident("_l", p); Ident("_s2", p)], p),
                    Call(Call(allocate, Ident("_v", p), p), Ident("_s1", p), p)
                   , p),
                  Tuple([Ident("_l",p); Ident("_s2", p)], p), p)
            , p)
         , p)
    | Bang(x, er) ->
      Fun(memory_name,
          In(Let(Tuple([Ident("_l", p); Ident("_s1", p)], p),
                 Call(aux x, memory_name, p), p),
             In(Let(Ident("_v", p), 
                    Call(Call(read, Ident("_l",p ),p), Ident("_s1", p), p), p)
               , Tuple([Ident("_v", p); Ident("_s1", p)], p), p), p), p)

    | MainSeq(a, b, er) | Seq(a, b, er) ->
      Fun(memory_name, Call(aux (
        In(Let(Underscore, a, p), b, er)
        ), memory_name, p), p)

(* we put the fun s -> at the end of the function calls: exemple
   fun x -> fun y -> expr is transform in fun x -> fun y -> fun s -> [|expr|] s *)
    | Fun(arg, expr, er) ->
      Fun(memory_name, Tuple([Fun(arg, aux expr, p); memory_name], p), p)
    | Call(a, b, er) -> 
      (* f x <=> fun s -> let x1, s1 = [|x|] s in let x2, s2 = f s1 x1)*)

      Fun(memory_name, 
          In(Let(Tuple([Ident("_f1", p); Ident("_s1", p)], p), Call(aux a, memory_name, p), p),
             In( Let(Tuple([Ident("_v2", p); Ident("_s2", p)], p), Call(aux b, Ident("_s1", p), p), p),
                Call(Call(Ident("_f1", p), Ident("_v2", p), p), Ident("_s2", p), p),p ), p ), p)

    | IfThenElse (cond, a, b, er) ->
      Fun(memory_name,
          In(Let(Tuple([Ident("_c1", p); Ident("_s1", p)], p),
                 Call(aux cond, memory_name, p), p),
             IfThenElse(Ident("_c1", p),
                        Call(aux a, Ident("_s1", p), p),
                       Call(aux b, Ident("_s1", p), p), p), p
            ), p
         )
    | Raise(expr, er) ->
      Fun(memory_name, 
          In(Let(Tuple([Ident("_c1", p); Ident("_s1", p)], p),
                 Call(aux expr, memory_name, p), p),
             Tuple([Raise(Ident("_c1", p), er); Ident("_s1", p)], p)
               ,p),p)
    | Not (expr, er) ->
      Fun(memory_name, 
          In(Let(Tuple([Ident("_c1", p); Ident("_s1", p)], p),
                 Call(aux expr, memory_name, p), p),
             Tuple([Not(Ident("_c1", p), er); Ident("_s1", p)], p)
               ,p),p)
    | Printin (expr, er) ->
      Fun(memory_name, 
          In(Let(Tuple([Ident("_c1", p); Ident("_s1", p)], p),
                 Call(aux expr, memory_name, p), p),
             Tuple([Printin(Ident("_c1", p), er); Ident("_s1", p)], p)
               ,p),p)
    | ArrayMake (expr, er) ->
      Fun(memory_name, 
          In(Let(Tuple([Ident("_c1", p); Ident("_s1", p)], p),
                 Call(aux expr, memory_name, p), p),
             Tuple([ArrayMake(Ident("_c1", p), er); Ident("_s1", p)], p)
               ,p),p)

    | ArrayItem (ar, index, er) ->
      Fun(memory_name,
          In(
            Let(Tuple([Ident("_ar", p); Ident("_s1", p)],p), Call(aux ar, memory_name, p),p),
            In(
              Let(Tuple([Ident("_in", p); Ident("_s2", p)], p), Call(aux index, Ident("_s1", p), p), p),
              Tuple([ArrayItem(Ident("_ar", p), Ident("_in", p), p); Ident("_s2",p)], p)
               ,p)
               ,p),p)
            
    | ArraySet (ar, index, what, er) ->
      Fun(memory_name,
          In(
            Let(Tuple([Ident("_ar", p); Ident("_s1", p)],p), Call(aux ar, memory_name, p),p),
            In(
              Let(Tuple([Ident("_in", p); Ident("_s2", p)], p), Call(aux index, Ident("_s1", p), p), p),
              In( 
                Let(Tuple([Ident("_wh", p); Ident("_s3", p)], p), Call(aux what, Ident("_s2", p), p), p),
              Tuple([ArraySet(Ident("_ar", p), Ident("_in", p), Ident("_wh",p), p); Ident("_s3",p)], p)
               ,p)
               ,p),p),p)

    | TryWith(tr, pattern, expr, er) -> failwith "trywith not implemented"

    | LetRec _ | In _ -> failwith "syntax"

  in let code = aux code
  in Call(code, Unit, p)

