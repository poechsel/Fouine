open Env

type expr = 
    | Const     of int
    | Ident       of string
    | Unit
    | Not       of expr
    | Add      of expr * expr
    | Minus     of expr * expr
    | Mul      of expr * expr
    | In        of expr * expr
    | Eq        of expr * expr
    | Neq       of expr * expr
    | Gt       of expr * expr
    | Sgt       of expr * expr
    | Lt      of expr * expr
    | Slt        of expr * expr
    | And       of expr * expr
    | Or        of expr * expr
    | Let       of expr * expr
    | LetRec       of expr * expr
    | Call      of expr * expr 
    | TryWith of expr * expr * expr
    | Raise of expr
    | Bang of expr
    | Ref of expr
    | IfThenElse of expr * expr * expr
    | RefLet of expr * expr
(*    | Raise of expr
    | TryWith of expr * error * expr
  *)  | Fun of expr * expr
    | Printin of expr
    | Closure of expr * expr * expr Env.t
    | RecThing of expr * expr * expr Env.t
                   

let green = 32
let red = 31
let yellow = 33
let blue = 34
let magenta = 35
let cyan = 36
let lightgray = 37
let darkgray = 90
let lightred = 91
let lightgreen = 92
let lightyellow = 93
let lightblue = 94
let lightmagenta = 95
let lightcyan = 96
let colorate color  text = 
  "\027[" ^ string_of_int color ^ "m" ^ text ^ "\027[39m"




let rec beautyfullprint program = 
  let rec aux program ident = 
    match program with
  | Const       (x)         -> colorate magenta (string_of_int x)
  | Ident       (x)         -> x
  | Unit                    -> Printf.sprintf "Unit "
  | Add         (a, b)      -> Printf.sprintf "%s %s %s" (aux a ident) (colorate lightyellow "+") (aux b ident)
  | Mul         (a, b)      -> Printf.sprintf "%s %s %s" (aux a ident) (colorate lightyellow "*") (aux b ident)
  | Minus       (a, b)      -> Printf.sprintf "%s %s %s" (aux a ident) (colorate lightyellow "-") (aux b ident)
  | Sgt       (a, b)      -> Printf.sprintf "%s %s %s" (aux a ident) (colorate lightyellow ">") (aux b ident)
  | Gt       (a, b)      -> Printf.sprintf "%s %s %s" (aux a ident) (colorate lightyellow ">=") (aux b ident)
  | Slt       (a, b)      -> Printf.sprintf "%s %s %s" (aux a ident) (colorate lightyellow "<") (aux b ident)
  | Lt       (a, b)      -> Printf.sprintf "%s %s %s" (aux a ident) (colorate lightyellow "<=") (aux b ident)
  | Neq       (a, b)      -> Printf.sprintf "%s %s %s" (aux a ident) (colorate lightyellow "<>") (aux b ident)
  | Eq       (a, b)      -> Printf.sprintf "%s %s %s" (aux a ident) (colorate lightyellow "=") (aux b ident)
  | Or       (a, b)      -> Printf.sprintf "%s %s %s" (aux a ident) (colorate lightyellow "||") (aux b ident)
  | And       (a, b)      -> Printf.sprintf "%s %s %s" (aux a ident) (colorate lightyellow "&&") (aux b ident)
  | In          (a, b)      -> Printf.sprintf "%s \n%s%s %s)" (aux a ident) ident (colorate lightyellow "in") (aux b ident)
  | Let         (a, b)      -> Printf.sprintf "%s %s %s %s" (colorate lightyellow "let") (aux a ident) (colorate lightyellow "=") (aux b ident)
  | LetRec         (a, b)      -> Printf.sprintf "%s %s %s %s" (colorate lightyellow "let rec") (aux a ident) (colorate lightyellow "=") (aux b ident)
  | Call        (a, b)      -> Printf.sprintf "%s (%s)" (aux a ident) (aux b ident)
  | IfThenElse  (a, b, c)   -> Printf.sprintf "\n%sif %s then\n%s  %s\n%selse\n%s  %s" 
                              ident (aux a (ident^"  ")) ident (aux b (ident^"  ")) ident
                              ident (aux c (ident^"  "))
  | Fun         (a, b)      -> Printf.sprintf "%s %s %s" (aux a ident) (colorate lightyellow "->") (aux b ident)
  | Ref         (x)         -> Printf.sprintf "%s (%s)" (colorate lightblue "ref") (aux x ident) 
  | Raise       (x)         -> Printf.sprintf "%s (%s)" (colorate red "raise") (aux x ident)
  | TryWith     (a, b, c)   -> Printf.sprintf "\n%stry\n%s\n%swith E %s ->\n%s\n"
      ident (aux a (ident^"  ")) ident (aux b ident) (aux c (ident ^ "  "))
  | RefLet      (a, b)      -> Printf.sprintf "%s %s %s" (aux a ident) (colorate lightblue ":=") (aux b ident)
  | Bang        (x)         -> Printf.sprintf "%s%s" (colorate lightblue "!") (aux x ident)
  | Not        (x)         -> Printf.sprintf "not %s" (aux x ident)
  | Closure (id, expr, _)->Printf.sprintf "Closure(%s, %s)" (aux id ident) (aux expr ident)
  | Printin (_) -> Printf.sprint "Printin, please implement "

  in aux program ""
