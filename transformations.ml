open Prettyprint
open Shared.Env
open Expr
open Shared


module type Transform = sig
    val t_type : type_listing -> type_listing
    val t_buildin : fouine_values -> fouine_values
    val t_decl : fouine_values expr -> fouine_values expr
    val t_expr : fouine_values expr -> fouine_values expr
end 





module TransformRef : Transform = struct
  (* shortcuts *)
  let p = Lexing.dummy_pos
  let memory_name = Ident(([], "tr_memory"), p)
  (* our buildins functions to simulate refs *)
  let allocate = Ident(([], "buildins_allocate"), p)
  let read = Ident(([], "buildins_read"), p)
  let modify = Ident(([], "buildins_modify"), p)
  let create = Ident(([], "buildins_create"), p)

  (* transform a type accordingly to this transformation *)
  let rec t_type t =
    match t with
    | Fun_type(a, b) -> let temp = Generic_type (new_generic_id ())
      in Fun_type(t_type a, Fun_type(temp, Tuple_type([t_type b; temp])))
    | _ -> t


  let t_buildin buildin =
    match buildin with
    | FBuildin fct ->
      FBuildin(fun x -> FClosure(Ident(([], "x"), Lexing.dummy_pos), Tuple([Value (fct x); Ident(([], "x"), Lexing.dummy_pos)], Lexing.dummy_pos), Env.create))
    | _ -> failwith "a"

  let rec t_decl n = match n with
    | FixedType (Ident _ as t, x, e) -> let _ = print_endline @@ "transforming " ^ (print_type x) in  FixedType (t, t_type x, e)
    | _ -> n
  and
    (* refs will be representend by a const equivalent to a pointer. We use inference to make sure that the typing is correct *)
    t_expr code =
    let rec aux code = 
      match code with
      | Module (name, l, co, er) ->
        Module(name, List.map t_expr l, co, er)
      | FixedType (t, x, e) -> let _ = print_endline @@ "transforming " ^ (print_type x) in  FixedType (t_expr t, t_type x, e)
      | Const _ -> Fun(memory_name, Tuple([code; memory_name], p), p)
      | Bool _ -> Fun(memory_name, Tuple([code; memory_name], p), p)
      | Unit -> Fun(memory_name, Tuple([code; memory_name], p), p)
      | Underscore -> Fun(memory_name, Tuple([code; memory_name], p), p)
      | TypeDecl _ -> code
      | Constructor (_, None, _) -> Fun(memory_name, Tuple([code; memory_name], p), p)
      | Constructor (name, Some expr, error) ->
        Fun(memory_name, 
            In(Let(Tuple([Ident(([], "tr_v1"), p); Ident(([], "tr_s1"), p)], p),
                   Call(aux expr, memory_name, p), p),
               Tuple([Constructor(name, Some(Ident(([], "tr_v1"), p)), error); Ident(([], "tr_s1"), p)], p), p)
           , p)
      | Tuple (l, p) -> 
        let rec aux_tuple l e  acc i = begin match l with
          | [] -> 
            Tuple([Tuple(List.rev acc, p); e], p)
          | x::t -> 
            In(Let(Tuple([Ident(([], "tr_v"^string_of_int i), p); 
                          Ident(([], "tr_s"^string_of_int i), p)], p), 
                   Call(aux x, e, p), p),
               aux_tuple t (Ident(([], "tr_s"^string_of_int i), p)) 
                 (Ident(([], "tr_v"^string_of_int i), p)::acc) (i+1), 
               p)
        end 
        in Fun(memory_name, aux_tuple l memory_name [] 0, p)

      | MatchWith(expr, pattern_actions, err) ->
        Fun(memory_name,
            In(Let(Tuple([Ident(([], "tr_v1"), p); Ident(([], "tr_s1"), p)], p),
                   Call(aux expr, memory_name, p), p),
               MatchWith(Ident(([], "tr_v1"), p),
                         List.map (fun (a, b) -> t_decl a, Call(aux b, Ident(([], "tr_s1"), p), p)) 
                           pattern_actions
                        , p)
              , p),p)

      | Ident _ -> Fun(memory_name, Tuple([code; memory_name], p), p)

      | BinOp(x, a, b, er) when x#symbol = ":=" -> 
        Fun (memory_name,
             In(Let(Tuple([Ident(([], "tr_l1"), p); Ident(([], "tr_s1"), p)], p),
                    Call(aux a, memory_name, p), p),
                In(Let(Tuple([Ident(([], "tr_v2"), p); Ident(([], "tr_s2"), p)], p),
                       Call(aux b, Ident(([], "tr_s1"), p), p), p),
                   In(Let(Ident(([], "tr_s3"), p), 
                          Call(Call(modify,
                                    Ident(([], "tr_s2"), p), p),
                               Tuple([Ident(([], "tr_l1"), p); Ident(([], "tr_v2"), p)], p), p)
                         , p),
                      Tuple([Ident(([], "tr_v2"), p); Ident(([], "tr_s3"), p)], p), p),p),p),p)

      | BinOp(x, a, b, er) ->
        Fun(memory_name, 
            In(Let(Tuple([Ident(([], "tr_f1"), p); Ident(([], "tr_s1"), p)], p), 
                   Call(aux a, memory_name, p), p),
               In(Let(Tuple([Ident(([], "tr_f2"), p); Ident(([], "tr_s2"), p)], p), 
                      Call(aux b, Ident(([], "tr_s1"), p), p), p),
                  Tuple([BinOp(x, Ident(([], "tr_f1"), p), Ident(([], "tr_f2"), p), er); 
                         Ident(([], "tr_s2"), p)], p), p), p ), p)
      | Let(a, b, er) ->
        let a = t_decl a in 
        Let(Tuple([a; memory_name], p),
            aux b, p
           )

      (* because during parsing we transforms expressions of the form let rec f = thing in let f = thing, 
         a let rec declaration can't modify some ref values in itself. Then the transformed version of it is just a let rec with the momeory name as argument
      *)
      | LetRec(a, b, er) ->
        let a = t_decl a in
        aux (In(code, a, p))

      | In(Let(a, b, er), expr, _) ->
        let a = t_decl a in 
        Fun(memory_name, 
            In(Let (Tuple([Ident(([], "tr_x1"), p); Ident(([], "tr_s1"), p)], p), 
                    Call(aux b, memory_name, p), p),
               In(Let(a, Ident(([], "tr_x1"), p), er), 
                  Call(aux expr, Ident(([], "tr_s1"), p), p), p)
              ,p), p)

      | In(LetRec(a, Fun(arg, e, _), er), expr, _) ->
        let a = t_decl a in 
        Fun(memory_name, 
            In(LetRec(a, Fun(arg, aux e, p), p),
               Call(aux expr, memory_name, p)
              , p),p
           )


      | Ref (x, error_infos) -> 
        Fun(memory_name,
            In(Let(Tuple([Ident(([], "tr_v"), p); Ident(([], "tr_s1"), p)], p)
                  , Call(aux x, memory_name, p),p), 
               In(Let(Tuple([Ident(([], "tr_l"), p); Ident(([], "tr_s2"), p)], p),
                      Call(Call(allocate, Ident(([], "tr_v"), p), p), Ident(([], "tr_s1"), p), p)
                     , p),
                  Tuple([Ident(([], "tr_l"), p); Ident(([], "tr_s2"), p)], p), p)
              , p)
           , p)
      | Bang(x, er) ->
        Fun(memory_name,
            In(Let(Tuple([Ident(([], "tr_l"), p); Ident(([], "tr_s1"), p)], p),
                   Call(aux x, memory_name, p), p),
               In(Let(Ident(([], "tr_v"), p), 
                      Call(Call(read, Ident(([], "tr_l"),p ),p), Ident(([], "tr_s1"), p), p), p)
                 , Tuple([Ident(([], "tr_v"), p); Ident(([], "tr_s1"), p)], p), p), p), p)

      | MainSeq(a, b, er) | Seq(a, b, er) ->
        Fun(memory_name, Call(aux (
            In(Let(Underscore, a, p), b, er)
          ), memory_name, p), p)

      (* we put the fun s -> at the end of the function calls: exemple
         fun x -> fun y -> expr is transform in fun x -> fun y -> fun s -> [|expr|] s *)
      (* | BuildinClosure f ->
         Fun(memory_name, Tuple([Fun(memory_name, BuildinClosure f, p); memory_name], p), p)
      *)
      | Fun(arg, expr, er) ->
        let arg = t_decl arg in 
        Fun(memory_name, Tuple([Fun(arg, aux expr, p); memory_name], p), p)
      | Call(Constructor(name, None, error), b, er) ->
        aux (Constructor(name, Some b, error))
      | Call(a, b, er) -> 
        (* f x <=> fun s -> let x1, s1 = [|x|] s in let x2, s2 = f s1 x1)*)

        Fun(memory_name, 
            In(Let(Tuple([Ident(([], "tr_v2"), p); Ident(([], "tr_s1"), p)], p), 
                   Call(aux b, memory_name, p), p),
               In( Let(Tuple([Ident(([], "tr_f1"), p); Ident(([], "tr_s2"), p)], p), 
                       Call(aux a, Ident(([], "tr_s1"), p), p), p),
                   Call(Call(Ident(([], "tr_f1"), p), Ident(([], "tr_v2"), p), p), 
                        Ident(([], "tr_s2"), p), p),p ), p ), p)

      | IfThenElse (cond, a, b, er) ->
        Fun(memory_name,
            In(Let(Tuple([Ident(([], "tr_c1"), p); Ident(([], "tr_s1"), p)], p),
                   Call(aux cond, memory_name, p), p),
               IfThenElse(Ident(([], "tr_c1"), p),
                          Call(aux a, Ident(([], "tr_s1"), p), p),
                          Call(aux b, Ident(([], "tr_s1"), p), p), p), p
              ), p
           )
      | Raise(expr, er) ->
        Fun(memory_name, 
            In(Let(Tuple([Ident(([], "tr_c1"), p); Ident(([], "tr_s1"), p)], p),
                   Call(aux expr, memory_name, p), p),
               Tuple([Raise(Ident(([], "tr_c1"), p), er); Ident(([], "tr_s1"), p)], p)
              ,p),p)
      | Not (expr, er) ->
        Fun(memory_name, 
            In(Let(Tuple([Ident(([], "tr_c1"), p); Ident(([], "tr_s1"), p)], p),
                   Call(aux expr, memory_name, p), p),
               Tuple([Not(Ident(([], "tr_c1"), p), er); Ident(([], "tr_s1"), p)], p)
              ,p),p)
      | Printin (expr, er) ->
        Fun(memory_name, 
            In(Let(Tuple([Ident(([], "tr_c1"), p); Ident(([], "tr_s1"), p)], p),
                   Call(aux expr, memory_name, p), p),
               Tuple([Printin(Ident(([], "tr_c1"), p), er); Ident(([], "tr_s1"), p)], p)
              ,p),p)
      | ArrayMake (expr, er) ->
        Fun(memory_name, 
            In(Let(Tuple([Ident(([], "tr_c1"), p); Ident(([], "tr_s1"), p)], p),
                   Call(aux expr, memory_name, p), p),
               Tuple([ArrayMake(Ident(([], "tr_c1"), p), er); Ident(([], "tr_s1"), p)], p)
              ,p),p)

      | ArrayItem (ar, index, er) ->
        Fun(memory_name,
            In(
              Let(Tuple([Ident(([], "tr_ar"), p); Ident(([], "tr_s1"), p)],p), 
                  Call(aux ar, memory_name, p),p),
              In(Let(Tuple([Ident(([], "tr_in"), p); Ident(([], "tr_s2"), p)], p), 
                     Call(aux index, Ident(([], "tr_s1"), p), p), p),
                 Tuple([ArrayItem(Ident(([], "tr_ar"), p), Ident(([], "tr_in"), p), p); 
                        Ident(([], "tr_s2"),p)], p)
                ,p),p),p)

      | ArraySet (ar, index, what, er) ->
        Fun(memory_name,
            In(
              Let(Tuple([Ident(([], "tr_ar"), p); Ident(([], "tr_s1"), p)],p), 
                  Call(aux ar, memory_name, p),p),
              In(
                Let(Tuple([Ident(([], "tr_in"), p); Ident(([], "tr_s2"), p)], p), 
                    Call(aux index, Ident(([], "tr_s1"), p), p), p),
                In( 
                  Let(Tuple([Ident(([], "tr_wh"), p); Ident(([], "tr_s3"), p)], p), 
                      Call(aux what, Ident(([], "tr_s2"), p), p), p),
                  Tuple([ArraySet(Ident(([], "tr_ar"), p), Ident(([], "tr_in"), p), Ident(([], "tr_wh"),p), p); 
                         Ident(([], "tr_s3"),p)], p)
                  ,p)
                ,p),p),p)

      | TryWith(tr, pattern, expr, er) -> failwith "trywith not implemented"

      | In _ -> failwith "syntax"
      | _ -> failwith "it shouldn't had occured"

    in let code' = aux code
    in match code with
    | TypeDecl _ | Module _ -> code'
    | Let  _ -> begin match code' with 
        | Let(a, b, c) -> Let(a, Call(b, memory_name, p), p)
        | _ -> failwith "an other thing that wasn't supposed to happen"
      end
    | LetRec (temp, _, _) ->
      Let(temp, Call(Fun(Tuple([temp; Underscore], p), temp, p), Call(code', memory_name, p), p), p)
    | _ -> MainSeq(Let(Tuple([Ident(([], "tr_result"), p); memory_name], p), Call(code', memory_name
                                                                                 , p), p), Ident(([], "tr_result"), p), p)

end




























module TransformCps : Transform = struct
  (* define shortcuts for the rest of the code *)
  let p = Lexing.dummy_pos
  let k = Ident(([], "te_k"), p)
  let kE = Ident(([], "te_kE"), p)
  let create_wrapper content = Fun(k, Fun(kE, content, p), p)

  let y = Ident(([], "buildins_y"), p)


  (* transform a type and make it follow the transformation accordingly *)
  let rec t_type t =
    match t with
    | Fun_type(arg, out) -> 
      let a = Generic_type (new_generic_id ())
      in let b = Generic_type (new_generic_id ())
      in Fun_type(t_type arg, 
                  Fun_type(
                    Fun_type(t_type out, a),
                    Fun_type(b, a)))
    | _ -> t


  (* rename all occurence of a name inside a recursive function *)
  let rec rename_in_rec target_name name program = 
    let rename = rename_in_rec target_name name in
    match program with
    | FixedType (x, t, er) -> FixedType (rename x, t, er)
    | Ident _ when ident_equal program target_name -> name
    | Tuple (l, er) -> Tuple (List.map rename l, er)
    | Constructor(name, Some expr, er) -> Constructor(name, Some (rename expr), er)
    | Bang(x, er) -> Bang(rename x, er)
    | Ref (x, er) -> Ref(rename x, er)
    | Not (x, er) -> Not(rename x, er)
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
    | Seq(a, b, er) -> Seq(rename a, rename b, er)
    | MainSeq(a, b, er) -> MainSeq(rename a, rename b, er)
    | _ -> program


  let t_buildin buildin =

    match buildin with
    | FBuildin fct ->
      (* FBuildin (fun x ->  FClosure(Ident(([], "te_k"), p), Fun(Ident(([], "te_kE"), p),Call(k, Value (fct x) ,p),p), Env.create)   )  
      *)
      FBuildin (fun x->  FClosure(k, Fun(kE,Call(k, Value (fct x),p),p), Env.create)   )  
    | _ -> failwith "a"


  let rec t_decl n = match n with
    | FixedType (Ident _ as t, x, e) -> let _ = print_endline @@ "transforming " ^ (print_type x) in  FixedType (t, t_type x, e)
    | _ -> n
  and

    (* the transformation in itself *)
    t_expr code =
    let rec aux code =
      match code with 
      | FixedType(t, r, e) -> FixedType(aux t, t_type r, e)
      | Const _ -> create_wrapper (Call(k, code, p))
      | Bool _ -> create_wrapper (Call(k, code, p))

      | Ident _ -> create_wrapper (Call( k, code, p))
      | Underscore -> create_wrapper (Call(k, code, p))
      | Unit -> create_wrapper (Call(k, code, p))
      | Constructor (_, None, _) -> create_wrapper (Call(k, code, p))
      | Value _ -> create_wrapper (Call(k, code, p))

      | Tuple (l, er) ->
        begin
          let rec create_vars l i = 
            match l with
            | [] -> []
            | x::t -> Ident(([], "te_t_" ^ string_of_int i), p) :: create_vars t (i+1)
          in let vars = create_vars l 0
          in let out = Call(k, Tuple (List.fold_left (fun a b -> b :: a) [] (List.rev vars) , er), p)
          in let f = List.fold_right (fun (expr, var) b -> 
              Call(Call(aux expr, Fun(var, b, p), p), kE, p))

              (List.combine l vars) out

          in create_wrapper f
        end

      | Constructor(name, Some expr, er) ->
        create_wrapper @@
        Call(Call(aux expr,
                  Fun(Ident(([], "te_e"), p), Call(k, Constructor(name, Some (Ident(([], "te_e"), p)), er), p), p)
                 , p), kE, p)


      | MatchWith (expr, pattern_actions, err) ->
        create_wrapper @@
        Call(Call(aux expr, 
                  Fun(Ident(([], "te_expr"), p),
                      MatchWith(expr, 
                                List.map (fun (pattern, action) -> (t_decl pattern,  Call(Call(aux (Ident(([], "te_expr"), p)), Fun(pattern, Call(Call(aux action, k, p), kE, p), p), p), kE, p)))
                                  pattern_actions, err), p)


                 , p), kE, p)


      | Module (name, l, co, er) ->
        Module(name, List.map t_expr l, co, er)

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
                  Fun(Ident(([], "te_cond"), p), 
                      IfThenElse(Ident(([], "te_cond"), p), 
                                 Call(Call(aux a, k, p), kE, p),
                                 Call(Call(aux b, k, p), kE, p),er), p)
                 , p),
             kE, p)
      | BinOp(x, a, b, er) ->
        create_wrapper @@
        Call(Call(aux a,
                  (Fun(Ident(([], "te_a"), p), 
                       Call(Call(aux b,
                                 Fun (Ident(([], "te_b"), p), Call(k, BinOp(x, Ident(([], "te_a"), p), Ident(([], "te_b"), p), er), p), p), p) , kE, p), p)), p), kE, p)
      | Fun(x, expr, er) ->
        let x = t_decl x in 
        create_wrapper @@
        Call(k, (Fun(x, aux expr, er)), p)
      | Call(Constructor(name, None, b), arg, er ) ->
        aux (Constructor(name, Some arg, b))

      | Call(x, e, er) ->
        create_wrapper @@
        Call(Call(aux e,
                  (Fun(Ident(([], "te_v2"), p), 
                       Call(Call(aux x,
                                 Fun (Ident(([], "te_f"), p), 
                                      Call(Call(Call(Ident(([], "te_f"), p), Ident(([], "te_v2"), p), p), k, p), 
                                           kE, p), p), p)
                           , kE, p), p)), p)
            , kE, p)



      | Let(x, e1, _) ->
        let x = t_decl x in
        Let (x, Call(Call(aux e1, Fun(Ident(([], "x"), p), Ident(([], "x"), p), p), p), Fun(Ident(([], "x"), p), Ident(([], "x"), p),p), p),p)



      | In(Let(x, e1, _), e2, _) ->
        let x = t_decl x in 
        create_wrapper @@
        Call(Call(aux e1,
                  Fun(x, Call(Call(aux e2, k, p), kE, p), p), p), kE, p)


      | In(LetRec(x, e1, _), e2, _) -> begin
          let x = t_decl x in 
          match x with 
          | Ident((l, name), er) as old_name ->
            let new_name = Ident((l, "t_" ^ name), p) in
            let code = 
              In(Let(x,
                     In(Let(
                         x,
                         Fun(new_name, 
                             rename_in_rec old_name new_name e1, p), p),
                        Call(y, x, p)
                       ,p), p
                    ), e2, p)
            in aux code

          | _ -> failwith "errhor"
        end
      (* very buggy, but I don't know why *)
      | LetRec(x, e1, _) -> begin
          let x = t_decl x in 
          match x with 
          | Ident((l, name), er) as old_name ->
            let new_name = Ident((l, "t_" ^ name), p) in
            let code = 
              Let(x,
                  In(Let(
                      x,
                      Fun(new_name, 
                          rename_in_rec old_name new_name e1, p), p),
                     Call(y, x, p)
                    ,p), p
                 )
            in aux code
          (* LetRec(x, Call(Call(aux e1, Fun(Ident(([], "x"), p), Ident(([], "x"), p), p), p), Fun(Ident(([], "x"), p), Ident(([], "x"), p), p), p), p)*)
          | _ -> failwith "errhor"
        end
      | Printin(expr, er) ->
        create_wrapper @@
        Call(Call(aux expr,
                  Fun(Ident(([], "te_e"), p), Call(k, Printin(Ident(([], "te_e"), p), p), er), p)
                 , p), kE, p)
      | ArrayMake(expr, er) ->
        create_wrapper @@
        Call(Call(aux expr,
                  Fun(Ident(([], "te_e"), p), Call(k, ArrayMake(Ident(([], "te_e"), p), er), p), p)
                 , p), kE, p)
      | Not(expr, er) ->
        create_wrapper @@
        Call(Call(aux expr,
                  Fun(Ident(([], "te_e"), p), Call(k, Not(Ident(([], "te_e"), p), er), p), p)
                 , p), kE, p)

      | ArrayItem(ar, index, er) ->
        create_wrapper @@
        Call(Call(aux ar,
                  Fun(Ident(([], "te_ar"), p),
                      Call(Call(aux index,
                                Fun(Ident(([], "te_index"), p),
                                    Call(k, ArrayItem(Ident(([], "te_ar"), p), Ident(([], "te_index"), p), er), p),
                                    p), p), kE, p), p), p), kE, p)
      | ArraySet(ar, index, what, er) ->
        create_wrapper @@
        Call(Call(aux ar,
                  Fun(Ident(([], "te_ar"), p),
                      Call(Call(aux index,
                                Fun(Ident(([], "te_index"), p),
                                    Call(Call(aux what, 
                                              Fun(Ident(([], "te_what"), p),
                                                  Call(k, ArraySet(Ident(([], "te_ar"), p), Ident(([], "te_index"), p), Ident(([], "te_what"), p), er), p),
                                                  p), p), kE, p), p), p), kE, p), p), p), kE, p)
      | Bang(expr, er) ->
        create_wrapper @@
        Call(Call(aux expr,
                  Fun(Ident(([], "te_e"), p), Call(k, Bang(Ident(([], "te_e"), p), er), p), p)
                 , p), kE, p)
      | Ref(expr, er) ->
        create_wrapper @@
        Call(Call(aux expr,
                  Fun(Ident(([], "te_e"), p), Call(k, Ref(Ident(([], "te_e"), p), er), p), p)
                 , p), kE, p)

      | Seq(expr1, expr2, er) | MainSeq(expr1, expr2, er) ->
        create_wrapper @@
        Call(Call(aux expr1, 
                  Fun(Underscore, Call(Call(aux expr2, k, p), kE, p), p), p), kE, p)
      | In(_, _, _) -> failwith "error"

      | _ -> failwith (pretty_print code ^"not implemented for exception transformation")

    in let x = Ident(([], "te_x"), p)
    in match code with
    | TypeDecl _ -> code
    | Module _ | LetRec _ | Let _ -> aux code (* we do not want to evaluate let and letrecs at first *)
    | _ -> Call(Call(aux code, Fun(x, x, p), p), Fun(x, x, p), p)

end



module TransformBoth : Transform = struct

  let t_type t =
    TransformCps.t_type @@ TransformRef.t_type t
  let t_expr t =
    TransformCps.t_expr @@ TransformRef.t_expr t
  let t_decl t =
    TransformCps.t_decl @@ TransformRef.t_decl t

  let p = Lexing.dummy_pos
  let k = Ident(([], "te_k"), p)
  let kE = Ident(([], "te_kE"), p)

  let t_buildin buildin =
    let m = Ident(([], "tr_memory"), p) in
    let tr_v2 = Ident(([], "tr_v2"), p) in
    let tr_s2 = Ident(([], "tr_s2"), p) in
    let tr_s1 = Ident(([], "tr_s1"), p) in
    let tr_f1 = Ident(([], "tr_f1"), p) in
    match buildin with
    | FBuildin fct ->
(*
FBuildin(fun x -> 
FClosure(m, Tuple([Fun(k, Fun(m, 
Tuple([Fun(kE, 
    Fun(m, 
    In(Let(Tuple([tr_v2; tr_s1], p), Call(Fun(m,
    Tuple([Value(fct x); m], p), p), m, p), p),
    In(Let(Tuple([tr_f1; tr_s2], p), Call(Fun(m, 
    Tuple([k; m], p), p), tr_s1, p), p),
       Call(Call(tr_f1, tr_v2, p), tr_s2, p), p), p), p), p); m], p), p), p); m], p),  Env.create)
      )
*)

      FBuildin(fun x -> FClosure(m, Tuple([Fun(k, Fun(m, Tuple([Fun(kE, Fun(m, Call(Call(k, Value (fct x), p), m, p), p), p); m], p), p), p); m], p), Env.create))
    | _ -> failwith "a"

end
