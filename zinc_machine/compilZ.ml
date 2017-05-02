open Expr
open Binop
open Env
open DreamZ
open Stack
open Prettyprint
open IsaZ

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
        [CUR ( (tail_compile a) @ [RETURN] )]
    | LambdaR (a) ->
        [GRAB] @ [CLOSUREC (compile a) ]
    | Call (a, b, _) ->
        [PUSHMARK] @
        (compile b) @ [PUSH] @
        (compile a) @ [APPLY]
    | Let (a, _, _) ->
        (compile a) @
        [LET]
    | LetIn (a, b) ->
        (compile a) @
        [LET] @
        (compile b) @
        [ENDLET]
    | LetRecIn (a, b) ->
        [DUMMY] @ (compile a) @ [UPDATE] @ (compile b) @ [ENDLET]
    | (MainSeq (a, b, _) | Seq (a, b, _)) -> 
        (compile a) @
        (compile b)
    | IfThenElse (cond, a, b, _) ->
        (compile cond) @
        [PROG (compile a)] @
        [PROG (compile b)] @ [BRANCH]
    | _ -> failwith (Printf.sprintf "compilation not implemented on %s" (show_expr expr))   
  end

and tail_compile expr =
  begin
    match expr with (*
    | Let (a, b, _) ->
        (compile a) @ [LET] @
        (tail_compile b) *)
    | LetIn (a, b) -> 
        (compile a) @ [LET] @ 
        (tail_compile b)
    | LetRecIn (a, b) ->
        [DUMMY] @ (compile a) @ [UPDATE] @ (tail_compile b)
    | Lambda (a) -> [GRAB] @ (tail_compile a)
    | Call (a, b, _) ->
        (compile b) @ [PUSH] @
        (compile a) @ [APPTERM]
    | IfThenElse (cond, a, b, _) ->
        (compile cond) @ 
        [PROG (tail_compile a)] @
        [PROG (tail_compile b)] @ [BRANCH]
    | _ -> 
        (compile expr) @
        [RETURN]
  end
