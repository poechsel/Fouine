open Expr
open Errors

let rec print_binop program ident underlined_a underlined_b = 
  match program with
  | BinOp (op, a, b, _) ->
    let str_a  = pretty_print_aux a ident true
    in let str_a = match a with
        | BinOp(op', _, _, _) when op'#precedence <= op#precedence -> str_a
        | x when is_atomic x -> str_a
        | _ ->
          Printf.sprintf "(%s)" str_a
    in let str_b  = pretty_print_aux b ident true
    in let str_b = match b with
        | BinOp(op', _, _, _) when op'#precedence <= op#precedence -> str_b
        | x when is_atomic x -> str_b
        | _ ->
          Printf.sprintf "(%s)" str_b
    in Printf.sprintf "%s %s %s" (if not underlined_a then str_a else Format.underline str_a) (op#symbol) (if not underlined_b then str_b else Format.underline str_b)
  | _ -> ""


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
    in 
    (if underlined_id then Format.underline str_id else str_id) ^
    Format.colorate Format.green "." ^ "(" ^ 
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
  | Ident       (x, _)          -> x
  | RefValue (x)                -> 
    "ref: " ^ (pretty_print_aux !x ident inline)
  | Bool true                   -> Format.colorate Format.blue "true"
  | Bool false                  -> Format.colorate Format.blue "false"
  | Array x                     ->
    let len = Array.length x
    in let rec aux_ar i  = 
         if i >= len then ""
         else if i < 100 then
           string_of_int x.(i) ^ "; " ^ aux_ar (i+1) 
         else "..."
    in Printf.sprintf "[|%s|]" @@  aux_ar 0
  | Unit                        -> Format.colorate Format.blue "()"
  | Underscore                  -> "_"
  | BinOp (x, a, b, _)          -> print_binop program ident false false
  | In          (a, b, _)       -> 
    "("^pretty_print_aux a ident inline ^
    break_line inline ident ^
    Format.colorate Format.green "in " ^
    pretty_print_aux b ident inline^")"
  | Let         (a, b, _)       -> 
    Format.colorate Format.green "let " ^
    pretty_print_aux a ident inline ^
    Format.colorate Format.green " = " ^
    pretty_print_aux b ident inline
  | LetRec         (a, b, _)    -> 
    Format.colorate Format.green "let rec " ^
    pretty_print_aux a ident inline ^
    Format.colorate Format.green " = " ^
    pretty_print_aux b ident inline
  | Call        (a, b, _)       -> 
    let str_b = pretty_print_aux b ident inline
    in let str_b  = (if is_atomic b then str_b else Printf.sprintf "(%s)" str_b)
    in Printf.sprintf "%s %s" (pretty_print_aux a ident inline) str_b
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
    Format.colorate Format.lightred "raise " ^
    pretty_print_aux x ident inline
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
  | Closure (id, expr, _)       -> "fun"
  | ClosureRec (_, id, expr, _) -> "fun"
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
  | _ -> ""




let rec pretty_print program = 
    pretty_print_aux program "" false
