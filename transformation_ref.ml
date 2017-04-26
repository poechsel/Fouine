open Env
open Prettyprint
open Expr

let p = Lexing.dummy_pos
let memory_name = Ident(".memory", p)


(*
let allocate = Fun(Ident(".v", p), Fun(Ident(".s1", p), Tuple([Ref(Ident(".v", p), p); Ident(".s1", p)], p), p), p)
let read = Fun(Ident(".v", p), Fun(Ident(".s1", p), Bang(Ident(".v", p), p), p), p)
let modify =Fun(Ident(".s2", p), Fun(Tuple([Ident(".l1", p); Ident(".v2", p)], p), 
                                     Seq(BinOp(refSet, Ident(".l1", p), Ident(".v2", p), p), Ident(".s2", p), p), p),p)
*)
let allocate = Ident("buildins_allocate", p)
let read = Ident("buildins_read", p)
let modify = Ident("buildins_modify", p)
let create = Ident("buildins_create", p)


(* refs will be representend by a const equivalent to a pointer. We use inference to make sure that the typing is correct *)
let rec transform_ref code =
  let rec aux code = 
    match code with
    | Const _ -> Fun(memory_name, Tuple([code; memory_name], p), p)
    | Bool _ -> Fun(memory_name, Tuple([code; memory_name], p), p)
    | Unit -> Fun(memory_name, Tuple([code; memory_name], p), p)
    | Underscore -> Fun(memory_name, Tuple([code; memory_name], p), p)
    | TypeDecl _ -> Fun(memory_name, Tuple([code; memory_name], p), p)
    | Constructor_noarg _ -> Fun(memory_name, Tuple([code; memory_name], p), p)
    | Constructor (name, expr, error) ->
      Fun(memory_name, 
          In(Let(Tuple([Ident(".v1", p); Ident(".s1", p)], p),
                 Call(aux expr, memory_name, p), p),
             Tuple([Constructor(name, Ident(".v1", p), error); Ident(".s1", p)], p), p)
            , p)
    | Tuple (l, p) -> 
        let rec aux_tuple l e  acc i = begin match l with
          | [] -> Tuple([Tuple(List.rev acc, p); e], p)
    | x::t -> In(Let(Tuple([Ident(".v"^string_of_int i, p); Ident(".s"^string_of_int i, p)], p), Call(aux x, e, p), p),
                    aux_tuple t (Ident(".s"^string_of_int i, p)) (Ident(".v"^string_of_int i, p)::acc) (i+1), p)
        end in Fun(memory_name, aux_tuple l memory_name [] 0, p)
      
    | MatchWith(expr, pattern_actions, err) ->
      Fun(memory_name,
          In(Let(Tuple([Ident(".v1", p); Ident(".s1", p)], p),
                 Call(aux expr, memory_name, p), p),
             MatchWith(Ident(".v1", p),
                      List.map (fun (a, b) -> a, Call(aux b, Ident(".s1", p), p)) pattern_actions
                      , p)
         , p),p)
      
    | Ident _ -> Fun(memory_name, Tuple([code; memory_name], p), p)
    | RefValue _ -> 
      
      Fun(memory_name, Tuple([code; memory_name], p), p)
    | Array _ -> Fun(memory_name, Tuple([code; memory_name], p), p)

    | BinOp(x, a, b, er) when x#symbol = ":=" -> 
      Fun (memory_name,
           In(Let(Tuple([Ident(".l1", p); Ident(".s1", p)], p),
                  Call(aux a, memory_name, p), p),
             In(Let(Tuple([Ident(".v2", p); Ident(".s2", p)], p),
                    Call(aux b, Ident(".s1", p), p), p),
                In(Let(Ident(".s3", p), 
                       Call(Call(modify,
                                 Ident(".s2", p), p),
                            Tuple([Ident(".l1", p); Ident(".v2", p)], p), p)
                      , p),
                   Tuple([Ident(".v2", p); Ident(".s3", p)], p), p),p),p),p)

    | BinOp(x, a, b, er) ->
      Fun(memory_name, 
          In(Let(Tuple([Ident(".f1", p); Ident(".s1", p)], p), Call(aux a, memory_name, p), p),
             In( Let(Tuple([Ident(".f2", p); Ident(".s2", p)], p), Call(aux b, Ident(".s1", p), p), p),
                 Tuple([BinOp(x, Ident(".f1", p), Ident(".f2", p), er); Ident(".s2", p)], p), p), p ), p)
    | Let(a, b, er) ->
      Fun(memory_name, 
          In(Let (Tuple([Ident(".x1", p); Ident(".s1", p)], p), Call(aux b, memory_name, p), p),
             In(Let(a, Ident(".x1", p), er), Tuple([a; Ident(".s1", p)], p), p)
            ,p), p)
    | In(Let(a, b, er), expr, _) ->
      Fun(memory_name, 
          In(Let (Tuple([Ident(".x1", p); Ident(".s1", p)], p), Call(aux b, memory_name, p), p),
             In(Let(a, Ident(".x1", p), er), Call(aux expr, Ident(".s1", p), p), p)
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
          In(Let(Tuple([Ident(".v", p); Ident(".s1", p)], p)
                , Call(aux x, memory_name, p),p), 
             In(Let(Tuple([Ident(".l", p); Ident(".s2", p)], p),
                    Call(Call(allocate, Ident(".v", p), p), Ident(".s1", p), p)
                   , p),
                  Tuple([Ident(".l",p); Ident(".s2", p)], p), p)
            , p)
         , p)
    | Bang(x, er) ->
      Fun(memory_name,
          In(Let(Tuple([Ident(".l", p); Ident(".s1", p)], p),
                 Call(aux x, memory_name, p), p),
             In(Let(Ident(".v", p), 
                    Call(Call(read, Ident(".l",p ),p), Ident(".s1", p), p), p)
               , Tuple([Ident(".v", p); Ident(".s1", p)], p), p), p), p)

    | MainSeq(a, b, er) | Seq(a, b, er) ->
      Fun(memory_name, Call(aux (
        In(Let(Underscore, a, p), b, er)
        ), memory_name, p), p)

(* we put the fun s -> at the end of the function calls: exemple
   fun x -> fun y -> expr is transform in fun x -> fun y -> fun s -> [|expr|] s *)
    | Fun(arg, expr, er) ->
      Fun(memory_name, Tuple([Fun(arg, aux expr, p); memory_name], p), p)
    | Call(Constructor_noarg(name, error), b, er) ->
      aux (Constructor(name, b, error))
    | Call(a, b, er) -> 
      (* f x <=> fun s -> let x1, s1 = [|x|] s in let x2, s2 = f s1 x1)*)

      Fun(memory_name, 
          In(Let(Tuple([Ident(".f1", p); Ident(".s1", p)], p), Call(aux a, memory_name, p), p),
             In( Let(Tuple([Ident(".v2", p); Ident(".s2", p)], p), Call(aux b, Ident(".s1", p), p), p),
                Call(Call(Ident(".f1", p), Ident(".v2", p), p), Ident(".s2", p), p),p ), p ), p)

    | IfThenElse (cond, a, b, er) ->
      Fun(memory_name,
          In(Let(Tuple([Ident(".c1", p); Ident(".s1", p)], p),
                 Call(aux cond, memory_name, p), p),
             IfThenElse(Ident(".c1", p),
                        Call(aux a, Ident(".s1", p), p),
                       Call(aux b, Ident(".s1", p), p), p), p
            ), p
         )
    | Raise(expr, er) ->
      Fun(memory_name, 
          In(Let(Tuple([Ident(".c1", p); Ident(".s1", p)], p),
                 Call(aux expr, memory_name, p), p),
             Tuple([Raise(Ident(".c1", p), er); Ident(".s1", p)], p)
               ,p),p)
    | Not (expr, er) ->
      Fun(memory_name, 
          In(Let(Tuple([Ident(".c1", p); Ident(".s1", p)], p),
                 Call(aux expr, memory_name, p), p),
             Tuple([Not(Ident(".c1", p), er); Ident(".s1", p)], p)
               ,p),p)
    | Printin (expr, er) ->
      Fun(memory_name, 
          In(Let(Tuple([Ident(".c1", p); Ident(".s1", p)], p),
                 Call(aux expr, memory_name, p), p),
             Tuple([Printin(Ident(".c1", p), er); Ident(".s1", p)], p)
               ,p),p)
    | ArrayMake (expr, er) ->
      Fun(memory_name, 
          In(Let(Tuple([Ident(".c1", p); Ident(".s1", p)], p),
                 Call(aux expr, memory_name, p), p),
             Tuple([ArrayMake(Ident(".c1", p), er); Ident(".s1", p)], p)
               ,p),p)

    | ArrayItem (ar, index, er) ->
      Fun(memory_name,
          In(
            Let(Tuple([Ident(".ar", p); Ident(".s1", p)],p), Call(aux ar, memory_name, p),p),
            In(
              Let(Tuple([Ident(".in", p); Ident(".s2", p)], p), Call(aux index, Ident(".s1", p), p), p),
              Tuple([ArrayItem(Ident(".ar", p), Ident(".in", p), p); Ident(".s2",p)], p)
               ,p)
               ,p),p)
            
    | ArraySet (ar, index, what, er) ->
      Fun(memory_name,
          In(
            Let(Tuple([Ident(".ar", p); Ident(".s1", p)],p), Call(aux ar, memory_name, p),p),
            In(
              Let(Tuple([Ident(".in", p); Ident(".s2", p)], p), Call(aux index, Ident(".s1", p), p), p),
              In( 
                Let(Tuple([Ident(".wh", p); Ident(".s3", p)], p), Call(aux what, Ident(".s2", p), p), p),
              Tuple([ArraySet(Ident(".ar", p), Ident(".in", p), Ident(".wh",p), p); Ident(".s3",p)], p)
               ,p)
               ,p),p),p)

    | TryWith(tr, pattern, expr, er) -> failwith "trywith not implemented"

    | LetRec _ | In _ -> failwith "syntax"
    | _ -> failwith "it shouldn't had occured"

  in let code = aux code
  in In(Let(Tuple([Ident(".result", p); Ident(".env", p)], p), Call(code, create, p), p), Ident(".result", p), p)

