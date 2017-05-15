open Expr
open Shared
open Dream
open DreamEnv
open CompilB
open SecdB

let passed_bruijn x = true

let rec detect_jit e = 
  match e with
  | Const _ -> true
  | Bool _ -> true
  | Underscore -> true
  | Unit -> true
  | Seq (a, b, ld) -> (detect_jit a) && (detect_jit b) 
  | Not       (a, ld) ->  (detect_jit a)
  | In (Let (Ident _, b, _), c, _) -> (detect_jit b) && (detect_jit c)
  | In (LetRec (Ident _, b, _), c, _) ->   (detect_jit b) && (detect_jit c)
  | IfThenElse (a, b, c, ld) -> (detect_jit a) && (detect_jit b) && (detect_jit c)
  | Printin (a, ld) -> detect_jit a
  | BinOp (_, a, b, _) -> (detect_jit a) && (detect_jit b) 
  | In _ | Ident _ | Call _ | ArrayItem _ | ArraySet _ | Fun _ | RefLet _ | Bang _ | Ref _ | Tuple _ | MatchWith _ 
  | Open _ | Constructor _ | TypeDecl _ | FixedType _ | Eol _ | ArrayMake _ | Access _ | Lambda _ | LambdaR _
  | LetIn _ | LetRecIn _ | Bclosure _ | LetTup _ | LetInTup _ | TryWith _ | Raise _ | MainSeq _ | Let _ | LetRec _ -> false

let rec convert_jit e = 
  match e with
  | Open _ -> e 
(*  | Constructor of (a, b, c)
  | TypeDecl of type_listing * type_declaration * Lexing.position
  |  FixedType of 'a expr * type_listing * Lexing.position *)
  | Call      (a, b, ld) -> let a', b' = convert_jit a, convert_jit b in Call (a', b', ld)
  | ArrayItem (a, b, ld) -> let a', b' = convert_jit a, convert_jit b in ArrayItem (a', b', ld) 
  | ArraySet  (a, b, c, ld) -> let a', b', c' = convert_jit a, convert_jit b, convert_jit c in ArraySet (a', b', c', ld) 
  | Ident _ -> e 
  | Seq (a, b, ld) -> let a', b' = convert_jit a, convert_jit b in Seq(a', b', ld) 
  | Unit -> e
  | Not       (a, ld) -> let a' = convert_jit a in Not (a', ld) 
  | Let (a, b, ld1) -> let a', b' = convert_jit a, convert_jit b in Let (a', b', ld1)
  | LetRec (a, b, ld1) -> let a', b' = convert_jit a, convert_jit b in LetRec (a', b', ld1)
  | In (a, b, ld) -> let a', b' = convert_jit a, convert_jit b in In (a', b', ld)
  | Bang (a, ld) -> let a' = convert_jit a in Bang (a', ld) 
  | Ref (a, ld) -> let a' = convert_jit a in Ref (a', ld) 
  | IfThenElse (a, b, c, ld) -> let a', b', c' = convert_jit a, convert_jit b, convert_jit c in IfThenElse (a', b', c', ld) 
  | RefLet (a, b, ld) -> let a', b' = convert_jit a, convert_jit b in RefLet (a', b', ld) 
  | Fun (a, b, ld) -> let a', b' = convert_jit a, convert_jit b in Fun (a', b', ld) 
  | Printin (a, ld) -> let a' = convert_jit a in Printin (a', ld) 
  | ArrayMake (a, ld) -> let a' = convert_jit a in ArrayMake (a', ld) 
  | BinOp (op, a, b, ld) -> let a', b' = convert_jit a, convert_jit b in BinOp (op, a', b', ld)
  | Tuple (l, ld) -> Tuple ((List.map (fun a -> (convert_jit a)) l), ld)
  | TryWith (a, b, c, ld) -> let a', b', c' = convert_jit a, convert_jit b, convert_jit c in TryWith (a', b', c', ld)
  | Raise (a, ld) -> let a' = convert_jit a in Raise (a', ld) 
  | MainSeq (a, b, ld) -> let a', b' = convert_jit a, convert_jit b in MainSeq (a', b', ld)
  | MatchWith (a, l, ld) -> let a' = convert_jit a in MatchWith (a', (List.map (fun (a, b) -> (convert_jit a, convert_jit b)) l), ld)
  | Eol 
  | Const _  
  | Bool _
  | Underscore -> e 
  (* used for de bruijn indices preprocess *)
  | Access _ 
  | Lambda _
  | LambdaR _
  | LetIn _
  | LetRecIn _
  | LetTup _
  | Bclosure _
  | LetInTup _ -> failwith "Bruijn process instructions should not have appeared." 

exception NOT_PURE_FOUINE

let expr_of_item i =
  match i with
  | CST k -> Const k
  | BOOL b -> Bool b
  | _ -> raise NOT_PURE_FOUINE

let compile_jit code =
  if detect_jit code then
    let bytecode = compile code
    in Jit bytecode
  else
    raise NOT_PURE_FOUINE

let exec_jit_code e = 
  match e with
  | Jit bytecode -> 
      let resu = exec_wrap bytecode {debug = ref false ; nb_op = ref 0 ;
                                     jit = ref true ; t = 0.}
      in expr_of_item resu
  | _ -> raise NOT_PURE_FOUINE
