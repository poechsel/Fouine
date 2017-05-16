open Expr
open Dream
open Stack
open Prettyprint

let rec compile_Z expr =
  begin 
    match expr with
    | Const k -> [C k]
    | Bool b -> if b then [C 1] else [C 0]
    | TypeDecl _ -> []
    | Unit -> [PASS]
    | Underscore -> [PASS]
    | Ref (a, _) -> (compile_Z a) @ [REF] 
    | Bang (a, _) -> (compile_Z a) @ [BANG]
    | BinOp (op, e1, e2, _) ->
        (compile_Z e2) @ [PUSH] @
        (compile_Z e1) @ [BOP op] 
    | Ident (_, _) -> failwith "an ident was left"
    | Fun (_, _, _) -> failwith " a fun was kept "
    | In (a, b, _) -> print_endline @@ pretty_print expr ; failwith "in" 
    | Eol -> failwith "eol"
    | Access (n) -> [ACC n]
    | Lambda (a) ->
        [CUR ( (tail_compile_Z a) @ [RETURN] )]
    | LambdaR (a) ->
        [CLOSUREC (tail_compile_Z a) ] 
    | Bclosure x -> [BUILTIN x]
    | Call (a, b, _) ->
        [PUSHMARK] @
        (compile_Z b) @ [PUSH] @
        (compile_Z a) @ [APPLY]
    | Let (a, _, _) ->
        (compile_Z a) @
        [LET]
    | LetIn (a, b) ->
        (compile_Z a) @
        [LET] @
        (compile_Z b) @
        [ENDLET]
    | Printin(a, _) ->
        (compile_Z a) @
        [PRINTIN]
    | (MainSeq (a, b, _) | Seq (a, b, _)) -> 
        (compile_Z a) @
        (compile_Z b)
    | IfThenElse (cond, a, b, _) ->
        (compile_Z cond) @ [PUSH] @
        [PROG (compile_Z a)] @
        [PROG (compile_Z b)] @ [BRANCH]
    | _ -> failwith (Printf.sprintf "compilation not implemented on %s" (show_expr expr))   
  end

and tail_compile_Z expr =
  begin
    match expr with (*
    | Let (a, b, _) ->
        (compile_Z a) @ [LET] @
        (tail_compile_Z b) *)
    | LetIn (a, b) -> 
        (compile_Z a) @ [LET] @ 
        (tail_compile_Z b)
    | LetRecIn (a, b) ->
        [DUMMY] @ (compile_Z a) @ [UPDATE] @ (tail_compile_Z b)
    | Lambda (a) -> [GRAB] @ (tail_compile_Z a)
    | LambdaR (a) -> [GRAB] @ (tail_compile_Z a)
    | Call (a, b, _) ->
        (compile_Z b) @ [PUSH] @
        (compile_Z a) @ [APPTERM]
    | IfThenElse (cond, a, b, _) ->
        (compile_Z cond) @ [PUSH] @ 
        [PROG (tail_compile_Z a)] @
        [PROG (tail_compile_Z b)] @ [BRANCH]
    | _ -> 
        (compile_Z expr) @ [RETURN]
  end
