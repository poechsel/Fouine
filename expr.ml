type Expr = 
    | Const     of int
    | Var       of string
    | Uminus    of Expr
    | Not       of Expr
    | Plus      of Expr * Expr
    | Minus     of Expr * Expr
    | Mult      of Expr * Expr
    | Eq        of Expr * Expr
    | Geq       of Expr * Expr
    | Gt        of Expr * Expr
    | Leq       of Expr * Expr
    | Lt        of Expr * Expr
    | And       of Expr * Expr
    | Or        of Expr * Expr
    | RefAf     of Expr * Expr
    | RefGet    of Expr


type Error =
    | E of int

type Prog =
    | IfThenElse of Expr * Prog * Prog
    | LetIn of Expr * Expr
    | EndToken
    | ProgList of Prog list (* for expr ; expr <- extension 2 *)
    | Raise of Expr
    | TryWith of Prog * Error * Prog




type MathExpr = 
    | Const of int
    | 
    | Var of string
;;
