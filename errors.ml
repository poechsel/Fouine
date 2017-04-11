open Lexing


(* small module to format some text *)
module Format = struct
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

  let color_enabled = ref false
  let colorate color  text = 
    if !color_enabled then
    "\027[" ^ string_of_int color ^ "m" ^ text ^ "\027[39m"
    else  text

  let underline text = 
    "\027[4m" ^ text ^ "\027[0m"

end

(* creating all of our errors *)
exception InterpretationError of string
exception ParsingError of string

(* error of parsing *)
let send_parsing_error infos token = 
  ParsingError (Format.colorate Format.red "[Parsing Error]" ^ Printf.sprintf " %s line %d, character %d : error when seeing token %s" infos.pos_fname infos.pos_lnum (1 + infos.pos_cnum - infos.pos_bol) token)


let send_error str infos = 
  InterpretationError (Format.colorate Format.red "[Error]" ^ Printf.sprintf " %s line %d, character %d : %s" infos.pos_fname infos.pos_lnum (1 + infos.pos_cnum - infos.pos_bol) str)


(* an inference error can have three type:
   - a msg, which is a string. It is a final and fully treated error
   - a unification error if two types can't be unified
   - a speccomparer error: it is raised when their is a unifcation error
    during nested calls ending with a specomparer. It means the current call hasn't the
    same type than the compared type *)
type inferrorinfo = 
  | Msg of string
  | UnificationError
  | SpecComparerError

exception InferenceError of inferrorinfo
let send_inference_error infos token = 
  InferenceError (Msg (Format.colorate Format.red "[Error]" ^ Printf.sprintf " %s line %d, character %d : %s" infos.pos_fname infos.pos_lnum (1 + infos.pos_cnum - infos.pos_bol) token))


