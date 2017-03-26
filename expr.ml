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
    | FunRec of expr * expr



let rec beautyfullprint program = 
  let rec aux program ident = 
    match program with
  | Const       (x)         -> Printf.sprintf "[Const : %d] " x
  | Ident       (x)         -> Printf.sprintf "[Identifier: %s] " x
  | Unit                    -> Printf.sprintf "Unit "
  | Add         (a, b)      -> Printf.sprintf "%s + %s" (aux a ident) (aux b ident)
  | Mul         (a, b)      -> Printf.sprintf "%s * %s" (aux a ident) (aux b ident)
  | Minus       (a, b)      -> Printf.sprintf "%s - %s" (aux a ident) (aux b ident)
  | Sgt       (a, b)      -> Printf.sprintf "%s > %s" (aux a ident) (aux b ident)
  | Gt       (a, b)      -> Printf.sprintf "%s >= %s" (aux a ident) (aux b ident)
  | Slt       (a, b)      -> Printf.sprintf "%s < %s" (aux a ident) (aux b ident)
  | Lt       (a, b)      -> Printf.sprintf "%s <= %s" (aux a ident) (aux b ident)
  | Neq       (a, b)      -> Printf.sprintf "%s <> %s" (aux a ident) (aux b ident)
  | Eq       (a, b)      -> Printf.sprintf "%s = %s" (aux a ident) (aux b ident)
  | Or       (a, b)      -> Printf.sprintf "%s || %s" (aux a ident) (aux b ident)
  | And       (a, b)      -> Printf.sprintf "%s && %s" (aux a ident) (aux b ident)
  | In          (a, b)      -> Printf.sprintf "%s \n%sin %s" (aux a ident) ident (aux b ident)
  | Let         (a, b)      -> Printf.sprintf "let %s = %s" (aux a ident) (aux b ident)
  | Call        (a, b)      -> Printf.sprintf "%s (%s)" (aux a ident) (aux b ident)
  | IfThenElse  (a, b, c)   -> Printf.sprintf "\n%sif %s then\n%s  %s\n%selse\n%s  %s" 
                              ident (aux a (ident^"  ")) ident (aux b (ident^"  ")) ident
                              ident (aux c (ident^"  "))
  | Fun         (a, b)      -> Printf.sprintf "(%s -> %s)" (aux a ident) (aux b ident)
  | FunRec      (a, b)      -> Printf.sprintf "(%s Rec-> %s)" (aux a ident) (aux b ident)
  | Ref         (x)         -> Printf.sprintf "ref (%s)" (aux x ident)
  | Raise       (x)         -> Printf.sprintf "raise (%s)" (aux x ident)
  | TryWith     (a, b, c)   -> Printf.sprintf "\n%stry\n%s\n%swith E %s ->\n%s\n"
      ident (aux a (ident^"  ")) ident (aux b ident) (aux c (ident ^ "  "))
  | RefLet      (a, b)      -> Printf.sprintf "%s := %s" (aux a ident) (aux b ident)
  | Bang        (x)         -> Printf.sprintf "!%s" (aux x ident)
  | Not        (x)         -> Printf.sprintf "not %s" (aux x ident)

  in aux program ""
