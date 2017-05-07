open Expr
open Binop
open Env
open Dream
open Stack
open Prettyprint

(** COMPILING FUNCTION **)
(* its argument must come from convert_bruijn pre-process in bruijn.ml *)

let rec compile expr =
  begin 
    match expr with
    | Const k -> [C k]
    | Bool b -> if b then [C 1] else [C 0]
    | TypeDecl _ -> []
    | Unit -> [UNIT]
    | Underscore -> [PASS]
    | Ref (a, _) -> (compile a) @ [REF] 
    | Bang (a, _) -> (compile a) @ [BANG]
    | BinOp (op, e1, e2, _) ->
        (compile e2) @
        (compile e1) @ [BOP op]
    | Access (n) -> [ACC n]
    | Lambda (a) ->
        [CLOSURE (tail_compile a) ]
    | LambdaR (a) ->
        [CLOSUREC (tail_compile a) ]
    | Bclosure x -> [BUILTIN x] 
    | Call (a, b, _) ->
        (compile a) @
        (compile b) @
        [APPLY]
    | Let (a, _, _) ->
        (compile a) @
        [LET]
    | LetIn (a, b) ->
        (compile a) @
        [LET] @
        (compile b) @
        [ENDLET]
    | (MainSeq (a, b, _) | Seq (a, b, _)) -> 
        (compile a) @ (compile b)
    | IfThenElse (cond, a, b, _) ->
        (compile cond) @ 
        [PROG (compile a)] @
        [PROG (compile b)] @ [BRANCH]
    | TryWith(a, Const k, b, _) ->
        [PROG (compile a)] @
        [PROG ([C k] @ [BOP eqOp] @ [PROG (compile b)] @ [PROG [EXIT]] @ [BRANCH])] @
        [TRYWITH]
    | TryWith(a, id, b, _) ->
        [PROG (compile a)] @
        [PROG ( [CLOSURE ( (compile b) @ [RETURN])] @ [EXCATCH] )] @
        [TRYWITH]
    | Raise (a, _) ->
        (compile a) @ [EXIT]
    | ArrayItem(a, expr, _) ->
        (compile expr) @
        (compile a) @
        [ARRITEM]
    | ArraySet (a, expr, nvalue, _) ->
        (compile nvalue) @
        (compile expr) @
        (compile a) @
        [ARRSET]
    | ArrayMake (a, _) ->
        (compile a) @
        [AMAKE]
    | Printin (a, _) -> 
        (compile a) @ 
        [PRINTIN]
    | _ -> print_endline (Printf.sprintf "compilation not implemented on %s" (show_expr expr)); [] 
  end

(* mutual compiling function for TAIL-CALL optimization *)
(* very important for not overloading the stack on recursive functions *)

and tail_compile expr =
  begin
    match expr with
    | LetIn (a, b) ->
        (compile a) @
        [LET] @
        (tail_compile b)
    | Call (a, b, _) ->
        (compile a) @
        (compile b) @
        [TAILAPPLY]
    | IfThenElse (cond, a, b, _) ->
        (compile cond) @
        [PROG (tail_compile a)] @
        [PROG (tail_compile b)] @ [BRANCH]
    | _ -> 
        (compile expr) @
        [RETURN]
  end

