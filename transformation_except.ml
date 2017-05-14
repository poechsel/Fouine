open Prettyprint
open Shared.Env
open Expr
open Shared

(* define shortcuts for the rest of the code *)
let p = Lexing.dummy_pos
let k = Ident(([], "te_k"), p)
let kE = Ident(([], "te_kE"), p)
let create_wrapper content = Fun(k, Fun(kE, content, p), p)

let y = Ident(([], "buildins_y"), p)


(* transform a type and make it follow the transformation accordingly *)
let rec transform_exceptions_type t =
  match t with
  | Fun_type(arg, out) -> 
    let a = Generic_type (new_generic_id ())
    in let b = Generic_type (new_generic_id ())
    in Fun_type(transform_exceptions_type arg, 
                Fun_type(
                  Fun_type(transform_exceptions_type out, a),
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


let transform_buildin_exceptions buildin =

  match buildin with
  | FBuildin fct ->
   (* FBuildin (fun x ->  FClosure(Ident(([], "te_k"), p), Fun(Ident(([], "te_kE"), p),Call(k, Value (fct x) ,p),p), Env.create)   )  
      *)
    FBuildin (fun x->  FClosure(k, Fun(kE,Call(k, Value (fct x),p),p), Env.create)   )  
  | _ -> failwith "a"
let transform_buildin_all buildin =
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


let rec transform_exceptions_aux_decl n = match n with
    | FixedType (Ident _ as t, x, e) -> let _ = print_endline @@ "transforming " ^ (print_type x) in  FixedType (t, transform_exceptions_type x, e)
    | _ -> n
and

(* the transformation in itself *)
transform_exceptions code =
  let rec aux code =
    match code with 
    | FixedType(t, r, e) -> FixedType(aux t, transform_exceptions_type r, e)
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
                              List.map (fun (pattern, action) -> (transform_exceptions_aux_decl pattern,  Call(Call(aux (Ident(([], "te_expr"), p)), Fun(pattern, Call(Call(aux action, k, p), kE, p), p), p), kE, p)))
                                pattern_actions, err), p)


               , p), kE, p)


    | Module (name, l, co, er) ->
      Module(name, List.map transform_exceptions l, co, er)

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
      let x = transform_exceptions_aux_decl x in 
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
      let x = transform_exceptions_aux_decl x in
      Let (x, Call(Call(aux e1, Fun(Ident(([], "x"), p), Ident(([], "x"), p), p), p), Fun(Ident(([], "x"), p), Ident(([], "x"), p),p), p),p)



    | In(Let(x, e1, _), e2, _) ->
      let x = transform_exceptions_aux_decl x in 
      create_wrapper @@
      Call(Call(aux e1,
                Fun(x, Call(Call(aux e2, k, p), kE, p), p), p), kE, p)


    | In(LetRec(x, e1, _), e2, _) -> begin
      let x = transform_exceptions_aux_decl x in 
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
      let x = transform_exceptions_aux_decl x in 
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


