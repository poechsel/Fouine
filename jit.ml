open Expr
open Shared
open Dream

let passed_bruijn x = true

let rec detect_jit e = 
  match e with
  | Open _ -> false 
(*  | Constructor of identifier * 'a expr perhaps * Lexing.position (* a type represeting a construction in the form Constructor (name,parent, value) *)
  | TypeDecl of type_listing * type_declaration * Lexing.position
  | FixedType of 'a expr * type_listing * Lexing.position *)
  | Eol -> false
  | Const _ -> true 
  | Bool _ -> true 
  | Underscore -> true
  | ArrayItem (a, b, ld) -> (detect_jit a) && (detect_jit b)
  | ArraySet  (a, b, c, ld) -> (detect_jit a) && (detect_jit b) && (detect_jit c)
  | Ident (id, ld) -> if (passed_bruijn (string_of_ident id)) then true else false 
  | Seq (a, b, ld) -> (detect_jit a) && (detect_jit b)
  | Unit -> true
  | Not       (a, ld) ->  (detect_jit a)
  | In        (Let (a, b, _), c, _) -> (detect_jit a) && (detect_jit b) && (detect_jit c)
  | In (LetRec (a, b, _), c, _) ->  (detect_jit a) && (detect_jit b) && (detect_jit c)
  | In _ -> false
  | MainSeq (a, b, ld) -> false  (* maybe change *)
  | Let       (a, b, _) -> false 
  | LetRec       (a, b, ld) -> false
  | Call      (a, b, ld) -> true
  | TryWith (a, b, c, ld) -> (detect_jit a) && (detect_jit b) && (detect_jit c)
  | Raise (a, ld) -> false (* pour l'instant *)
  | Bang (a, ld) -> detect_jit a 
  | Ref (a, ld) -> detect_jit a
  | IfThenElse (a, b, c, ld) -> (detect_jit a) && (detect_jit b) && (detect_jit c)
  | RefLet (a, b, ld) -> false (* what ? *) 
  | Fun (a, b, ld) -> (detect_jit a) && (detect_jit b)
  | Printin (a, ld) -> detect_jit a
  | ArrayMake (a, ld) -> detect_jit a
  | BinOp (_, a, b, _) -> (detect_jit a) && (detect_jit b) 
  | Tuple (l, _) -> List.fold_left (fun a b -> a && (detect_jit b)) true l

(*  | MatchWith of 'a expr * ('a expr * 'a expr) list * Lexing.position *) (* not yet *)
  (* used for de bruijn indices preprocess *)
  | Access _ 
  | Lambda _
  | LambdaR _
  | LetIn _
  | LetRecIn _
  | Bclosure _
  | LetTup _
  | LetInTup _ -> failwith "wth ?" 
  | _ -> false
