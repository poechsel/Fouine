open Expr
open Binop
open Env
open Dream
open Stack
open Prettyprint
open IsaKrivine

let rec compile expr =
  begin 
    match expr with
    | Const k -> [C k]
    | Bool b -> if b then [C 1] else [C 0]
    | TypeDecl _ -> []
    | Unit -> [PASS]
    | Underscore -> [PASS]
    | Ref (a, _) -> (compile a) @ [REF] 
    | Bang (a, _) -> (compile a) @ [BANG]
    | BinOp (op, e1, e2, _) ->
        (compile e2) @
        (compile e1) @ [BOP op]
    | SpecComparer (_) -> failwith "spec comparer"
    | Ident (_, _) -> failwith "an ident was left"
    | Fun (_, _, _) -> failwith " a fun was kept "
    | In (a, b, _) -> print_endline @@ pretty_print expr ; failwith "in" 
    | Eol -> failwith "eol"
    | Access (n) -> [ACC n]
    | Lambda (a) ->
        [GRAB] @
        [CLOSURE (compile a) ]
    | LambdaR (a) ->
        [GRAB] @
        [CLOSUREC (compile a) ]
    | Call (a, b, _) ->
        [PUSH (compile b)] @
        (compile a)
    | LetRec (_, _, _) -> failwith "oyoy"
    | Let (a, _, _) ->
        (compile a) @
        [LET]
    | LetIn (a, b) ->
        (compile a) @
        [LET] @
        (compile b) @
        [ENDLET]
    | (MainSeq (a, b, _) | Seq (a, b, _)) -> 
        (compile a) @
        (compile b)
    | IfThenElse (cond, a, b, _) ->
        (compile cond) @
        [PROG (compile a)] @
        [PROG (compile b)] @ [BRANCH]
    | _ -> failwith (Printf.sprintf "compilation not implemented on %s" (show_expr expr))   
  end

  (*
and tail_compile expr =
  begin
    match expr with
    | Let (a, b, _) ->
        (compile a) @
        [LET] @
        (tail_compile b)
    | Call (a, b, _) ->
        (compile a) @
        (compile b) @
        [TAILAPPLY]
    | _ -> 
        (compile expr) @
        [RETURN]
  end
*)
