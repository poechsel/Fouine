open Lexer
open Commons
open Buildins
open Parser
open Expr
open Errors
open Shared
open Shared.Env


(*we define a lot of primitives for pretty print because in some case we want some text underlined, or colored... *)
(* it amount to a lot of code, because their is a lot of edge cases in doing a real pretty print *)
let rec print_binop program ident underlined_a underlined_b = 
  match program with
  | BinOp (op, a, b, _) ->
    let str_a  = pretty_print_aux a ident true
    in let str_a = match a with
        | BinOp(op', _, _, _) when op'#precedence >= op#precedence -> str_a
        | x when is_atomic x -> str_a
        | _ ->
          Printf.sprintf "(%s)" str_a
    in let str_b  = pretty_print_aux b ident true
    in let str_b = match b with
        | BinOp(op', _, _, _) when op'#precedence >= op#precedence -> str_b
        | x when is_atomic x -> str_b
        | _ ->
          Printf.sprintf "(%s)" str_b
    in Printf.sprintf "%s %s %s" (if not underlined_a then str_a else Format.underline str_a) (op#symbol) (if not underlined_b then str_b else Format.underline str_b)
  | _ -> ""

and pretty_print_infix_operator name a b ident underlined_a underlined_b =
  let p = Binop.get_operator_precedence name
  in let str_a  = pretty_print_aux a ident true
  in let str_a =
       if is_node_operator a then
         let _ = Printf.printf "a: %s" (str_a) in
         let p' = Binop.get_operator_precedence @@ get_operator_name a
         in if p' >= p then str_a else "("^str_a^")"
       else if is_atomic a then
         str_a
       else "("^str_a^")"
  in let str_b  = pretty_print_aux b ident true
  in let str_b = if is_node_operator b then
         let p' = Binop.get_operator_precedence (get_operator_name b)
         in if p' >= p then str_b else "("^str_b^")"
       else if is_atomic b then
         str_b
       else "("^str_b^")"
  in Printf.sprintf "%s %s %s" (if not underlined_a then str_a else Format.underline str_a) name (if not underlined_b then str_b else Format.underline str_b)


and break_line inline ident =
  if not inline then "\n"^ident else " "

and pretty_print_unop fun_name program color ident inline underlined = 
  let str_x = pretty_print_aux program ident inline
  in let str_x = if underlined then Format.underline str_x else str_x
  in Format.colorate color fun_name ^ (if is_atomic program then str_x else Printf.sprintf "(%s)" str_x)

and pretty_print_not x ident inline underlined =
  pretty_print_unop "not " x Format.green ident inline underlined

and pretty_print_bang x ident inline underlined =
  pretty_print_unop "!" x Format.green ident inline underlined

and pretty_print_amake x ident inline underlined =
  pretty_print_unop "aMake " x Format.yellow ident inline underlined

and pretty_print_prInt x ident inline underlined =
  pretty_print_unop "prInt " x Format.yellow ident inline underlined

and pretty_print_arrayitem program ident inline underlined_id underlined_index = 
  match program with
  | ArrayItem (id, index, _) ->
    let str_id = pretty_print_aux id ident inline
    in let str_index = pretty_print_aux index ident inline
    in "("^
       (if underlined_id then Format.underline str_id else str_id) ^
       Format.colorate Format.green ")." ^ "(" ^ 
       (if underlined_index then Format.underline str_index else str_index) ^
       ")"
  | _ -> ""

and pretty_print_arrayset program ident inline underlined_expr = 
  match program with
  | ArraySet (id, x, value, p) ->
    let str_value = pretty_print_aux value ident inline
    in
    pretty_print_arrayitem (ArrayItem(id, x, p)) ident inline false false ^
    Format.colorate Format.green " <- " ^
    (if underlined_expr then Format.underline str_value else str_value)
  | _ -> ""

and pretty_print_seq program ident inline =
  match program with
  | Seq (a, b, _) -> 
    (* disjonctions to add ';' only when needed *)
    let str_a = (match a with
        | Seq _ -> pretty_print_seq a ident inline
        | _ -> pretty_print_aux a ident inline
      ) 
    in let str_b = (match b with
        | Seq _ -> pretty_print_seq b ident inline
        | _ -> pretty_print_aux b ident inline
      )
    in 
    str_a ^ ";"^ 
    break_line inline ident ^
    str_b
  | _ -> ""

and pretty_print_aux program ident inline = 
  match program with
  | Const       (x)             -> Format.colorate Format.blue (string_of_int x)
  | FixedType (a, t, _) ->
    "(" ^ pretty_print_aux a ident inline ^ " : " ^ Types.print t ^ ")"
  | Ident       (n, _)          ->
    let x = string_of_ident n
    in if Binop.is_operator x then "( "^x^" )"
    else x
  | Bool true                   -> Format.colorate Format.blue "true"
  | Bool false                  -> Format.colorate Format.blue "false"
  | Unit                        -> Format.colorate Format.blue "()"
  | Underscore                  -> "_"
  | BinOp (x, a, b, _)          -> print_binop program ident false false
  | In          (a, b, _)       -> 
    pretty_print_aux a ident inline ^
    break_line inline ident ^
    Format.colorate Format.green "in " ^
    pretty_print_aux b ident inline 
  | Let         (a, b, _)       -> 
    Format.colorate Format.green "let " ^
    pretty_print_aux a ident inline ^
    Format.colorate Format.green " = " ^
    pretty_print_aux b ident inline ^ ""
  | LetRec         (a, b, _)    -> 
    Format.colorate Format.green "let rec " ^
    pretty_print_aux a ident inline ^
    Format.colorate Format.green " = " ^
    pretty_print_aux b ident inline 
  | Call(Ident((_, name) as i, _), a, _) when Binop.is_prefix_operator name ->
    let name = string_of_ident i
    in if is_atomic a then
      Printf.sprintf "%s %s" name (pretty_print_aux a ident inline)
    else 
      Printf.sprintf "%s (%s)" name (pretty_print_aux a ident inline)
  | Call(Call(Ident((_, name) as i, _), a, _), b, _) when Binop.is_infix_operator name ->
    let name = string_of_ident i
    in pretty_print_infix_operator name a b ident false false
  | Call        (a, b, _)       -> 
    let str_b = pretty_print_aux b ident inline
    in let str_b  = (if is_atomic b then str_b else Printf.sprintf "(%s)" str_b)
    in begin match a with
      | Fun _ -> Printf.sprintf "(%s) %s" (pretty_print_aux a ident inline) str_b
      | _ -> Printf.sprintf "(%s) %s" (pretty_print_aux a ident inline) str_b
    end
  | IfThenElse  (a, b, c, _)    -> 
    break_line inline ident ^
    Format.colorate Format.green "if " ^
    pretty_print_aux a (ident ^ "  ") inline ^
    Format.colorate Format.green " then" ^
    break_line inline (ident ^ "  ") ^
    pretty_print_aux b (ident ^ "  ") inline ^
    break_line inline (ident) ^
    Format.colorate Format.green "else" ^
    break_line inline (ident ^ "  ") ^
    pretty_print_aux c (ident ^ "  ")  inline
  | Fun         (a, b, _)       -> 
    Format.colorate Format.green "fun " ^
    pretty_print_aux a (ident ^ "  ") inline ^ 
    Format.colorate Format.green " -> " ^ 
    break_line inline (ident ^ "  ") ^ 
    pretty_print_aux b (ident ^ "  ") inline 
  | Ref         (x, _)          -> 
    Format.colorate Format.blue "ref " ^
    pretty_print_aux x ident inline
  | Raise       (x, _)          -> 
    Format.colorate Format.lightred "raise (E " ^
    pretty_print_aux x ident inline ^ ")"
  | TryWith     (a, b, c, _)    -> 
    Format.colorate Format.green "try" ^
    break_line inline (ident ^ "  ") ^
    pretty_print_aux a (ident ^ "  ") inline ^ 
    break_line inline ident ^
    Format.colorate Format.green "with " ^
    Format.colorate Format.lightred "E " ^
    pretty_print_aux b ident inline ^ 
    Format.colorate Format.green " ->" ^
    break_line inline (ident^"  ") ^
    pretty_print_aux c ident inline
  | RefLet      (a, b, _)       -> 
    pretty_print_aux a ident inline ^
    Format.colorate Format.green " = " ^
    pretty_print_aux b ident inline
  | Bang        (x, _)          -> 
    pretty_print_bang x ident inline false
  | Not        (x, _)           -> 
    pretty_print_not x ident inline false
  | Printin (expr, p)           -> 
    pretty_print_prInt expr ident inline false
  | ArrayMake (expr, _)         -> 
    pretty_print_amake expr ident inline false
  | ArrayItem (id, index, _)    -> 
    pretty_print_arrayitem program ident inline false false
  | ArraySet (id, x, index, p)  -> 
    pretty_print_arrayset program ident inline false
  | Seq (a, b, _)               -> 
    Format.colorate Format.green "begin" ^
    break_line inline (ident ^ "  ") ^
    pretty_print_seq program (ident^"  ") inline ^
    break_line inline ident ^
    Format.colorate Format.green "end" ^
    break_line inline ""
  | MainSeq (a, b, _) -> 
    pretty_print_aux a ident inline ^ ";;"^
    break_line inline ident ^ 
    pretty_print_aux b ident inline ^
    (match b with
     | MainSeq _ -> ""
     | _ -> ";;")
  | Tuple (l, _) -> "(" ^ 
                    List.fold_left (fun x y -> x ^ ", " ^ pretty_print_aux y ident inline) (pretty_print_aux (List.hd l) ident inline) (List.tl l) 
                    ^ ")"

  | TypeDecl (name, l, _) ->
    let type_str = begin
      match l with
      | Types.Constructor_list l -> List.fold_left (fun a b -> a ^ "\n| " ^ Types.print b) "" l
      | Types.Basic l -> Types.print l
      | Types.Module _ -> "module sig"
    end
    in Printf.sprintf "type %s = %s"
      (Types.print name)
      type_str
  | MatchWith (pattern, l, _) ->
    Printf.sprintf "match %s with %s"
      (pretty_print_aux pattern ident inline)
      (List.fold_left (fun a (b, c) -> a ^ "\n  | " ^ (pretty_print_aux b ident true)
                                       ^ " -> " ^ (pretty_print_aux c ("    "^ident) inline)
                      )  "" l)

  | Constructor(name, None, _)  when name = list_none ->
    Printf.sprintf "[]"
  | Constructor (name, Some (Tuple([a; b], _)), _) when name = list_elt ->
    Printf.sprintf("%s::%s") (pretty_print_aux a ident inline) (pretty_print_aux b ident inline)
  | Constructor (name, None, _) ->
    Printf.sprintf "%s" @@ string_of_ident name
  | Constructor (name, Some expr, _) ->
    Printf.sprintf "%s %s" (string_of_ident name)
      (pretty_print_aux expr ident inline)
  | Module (name, content, _, _) ->
    Format.colorate Format.green "module" ^
    " " ^ Format.colorate Format.yellow name ^
    Format.colorate Format.green " = " ^ Format.colorate Format.yellow "struct" ^
    List.fold_left  (fun a b -> a ^  break_line inline (ident ^ "  ") ^ pretty_print_aux b (ident ^ "  ") inline ) "" content ^
    break_line inline ident ^
    Format.colorate Format.yellow "end"

  | Value x -> print_value x
  | _ -> ""

and 
  (* finally, our pretty print function *)
  pretty_print program = 
  pretty_print_aux program "" false


and   print_value value =
  match value with
  | FInt x -> string_of_int x
  | FUnit -> "()"
  | FBool true -> "true"
  | FBool false -> "false"
  | FTuple l ->  "(" ^ List.fold_left (fun x y -> x ^ ", " ^ print_value y) (print_value (List.hd l)) (List.tl l) ^ ")"
  | FArray x -> 
    let len = Array.length x
    in let rec aux_ar i  = 
         if i >= len then ""
         else if i < 100 then
           string_of_int x.(i) ^ "; " ^ aux_ar (i+1) 
         else "..."
    in Printf.sprintf "[|%s|]" @@  aux_ar 0
  | FRef r -> Printf.sprintf "{contents = %s}" (print_value !r)
  | FConstructor(name, None)  when name = list_none ->
    Printf.sprintf "[]"
  | FConstructor (name, Some (FTuple([a; b]))) when name = list_elt ->
    Printf.sprintf("%s::%s") (print_value a) (print_value b)
  | FConstructor (name, None) ->
    string_of_ident name
  | FConstructor (name, Some x) ->
    Printf.sprintf "%s %s" (string_of_ident name) (print_value x)
  | FBuildin _ -> Printf.sprintf "<build>"

  | _ -> "<fun>"

