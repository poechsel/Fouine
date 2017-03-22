type expr = 
    | Const     of int
    | Var       of string
    | Uminus    of expr
    | Not       of expr
    | Plus      of expr * expr
    | Minus     of expr * expr
    | Mult      of expr * expr
    | Eq        of expr * expr
    | Geq       of expr * expr
    | Gt        of expr * expr
    | Leq       of expr * expr
    | Lt        of expr * expr
    | And       of expr * expr
    | Or        of expr * expr
    | RefAf     of expr * expr
    | RefGet    of expr


type error =
    | E of int

type prog =
    | IfThenElse of expr * prog * prog
    | LetIn of expr * prog
    | EndToken
    | ProgList of prog list (* for expr ; expr <- extension 2 *)
    | Raise of expr
    | TryWith of prog * error * prog




