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
    | Neq       of expr * expr
    | Gt       of expr * expr
    | Sgt       of expr * expr
    | Lt      of expr * expr
    | Slt        of expr * expr
    | And       of expr * expr
    | Or        of expr * expr
    | Let       of expr * expr
    | RefAf     of expr * expr
    | Call      of expr * expr 
    | TryWith of expr * expr * expr
    | Raise of expr
    | Bang of expr
    | Ref of expr
    | RefGet    of expr
    | E of int
    | Expr of expr
    | IfThenElse of expr * expr * expr
    | LetIn of expr * expr
    | EndToken
    | RefLet of expr * expr
    | ProgList of expr list (* for expr ; expr <- extension 2 *)
(*    | Raise of expr
    | TryWith of expr * error * expr
  *)  | Fun of expr * expr
    | FunUnit of expr * expr
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
  | In          (a, b)      -> Printf.sprintf "%s \n%sin %s" (aux a ident) ident (aux b ident)
  | Eq          (a, b)      -> Printf.sprintf "%s = %s" (aux a ident) (aux b ident)
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
  | _ -> failwith "not implemented"

  in aux program ""
