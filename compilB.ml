open Expr
open Binop
open Env
open Dream
open Stack
open Prettyprint
open Isa

let show_expr e =
  match e with
  | Open _ -> "open"
  | SpecComparer _ -> "spec comparer"
  | Eol -> "eol"
  | Const _ -> "const"
  | Bool _ -> "bool"
  | Underscore -> "underscore"
  | Array _ -> "array"
  | ArrayItem _ -> "array item"
  | ArraySet _ -> "arr set"
  | RefValue _ -> "refvalue"
  | Ident _ -> "ident"
  | Seq _ -> "seq"
  | Unit -> "unit"
  | Not _ -> "not"
  | In _ -> "in"
  | MainSeq _ -> "mainseq"
  | Let _ -> "let"
  | LetRec _ -> "letrec"
  | Call _ -> "call"
  | TryWith _ -> "trywwith"
  | Raise _ -> "raise"
  | Bang _ -> "bang"
  | Ref _ -> "ref"
  | IfThenElse _ -> "ifthenelse"
  | RefLet _ -> "reflet"
  | Fun _ -> "fun"
  | Printin _ -> "printin"
  | ArrayMake _ -> "arraymake"
  | Closure _ -> "closure"
  | ClosureRec _ -> "closureRec"
  | BuildinClosure _ -> "bdclosure"
  | BinOp _ -> "binop"
  | Tuple _ -> "tuple"
  | Access _ -> "access"
  | Lambda _ -> "lambda"
  | LambdaR _ -> "lambdaR"
  | LetIn _ -> "letin"
  | LetRecIn _-> "letrecin"

let rec compile expr =
  begin 
    match expr with
    | Const k -> [C k]
    | Bool b -> if b then [C 1] else [C 0]
    | Unit -> [PASS]
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
        [CLOSURE (tail_compile a) ]
    | LambdaR (a) ->
        [CLOSUREC (tail_compile a) ]
    | Call (a, b, _) ->
        (compile a) @
        (compile b) @
        [APPLY]
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

