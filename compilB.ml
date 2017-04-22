open Expr
open Binop
open Env
open Dream
open Stack
open Prettyprint
open Isa

let rec compile expr =
  begin 
    match expr with
    | Const k -> [C k]
    | BinOp (op, e1, e2, _) ->
        (compile e2) @
        (compile e1) @ [BOP op]
    | Access (n) -> [ACC n]
    | Lambda (a) ->
        [CLOSURE ( (compile a) @ [RETURN] )]
    | Call (a, b, _) ->
        (compile a) @
        (compile b) @
        [APPLY]
    | Let (a, b, _) ->
        (compile a) @
        [LET] @
        (compile b) @
        [ENDLET]
    | Seq (a, b, _) -> 
        (compile a) @
        (compile b)
    | _ -> failwith (Printf.sprintf "compilation not implemented on %s" (pretty_print expr))   
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
        (compile e) @
        [RETURN]
*)
