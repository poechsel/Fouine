type expr = 
    | Const     of int
    | Ident       of string
    | Unit
    | Uminus    of expr
    | Not       of expr
    | Add      of expr * expr
    | Minus     of expr * expr
    | Mul      of expr * expr
    | In        of expr * expr
    | Eq        of expr * expr
    | Geq       of expr * expr
    | Gt        of expr * expr
    | Leq       of expr * expr
    | Lt        of expr * expr
    | And       of expr * expr
    | Or        of expr * expr
    | Aff       of expr * expr
    | RefAf     of expr * expr
    | Call      of expr * expr 
    | RefGet    of expr
    | E of int
    | Expr of expr
    | IfThenElse of expr * expr * expr
    | LetIn of expr * expr
    | EndToken
    | ProgList of expr list (* for expr ; expr <- extension 2 *)
(*    | Raise of expr
    | TryWith of expr * error * expr
  *)  | Fun of expr * expr
    | FunUnit of expr * expr
    | FunRec of expr * expr




