open Lexing


(* small module to format some text *)
module Format = struct
  let green        = 32
  let red          = 31
  let yellow       = 33
  let blue         = 34
  let magenta      = 35
  let cyan         = 36
  let lightgray    = 37
  let darkgray     = 90
  let lightred     = 91
  let lightgreen   = 92
  let lightyellow  = 93
  let lightblue    = 94
  let lightmagenta = 95
  let lightcyan    = 96

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
exception LoadModule of string * string

(* error of parsing *)
let send_parsing_error infos token = 
  ParsingError 
    (Format.colorate Format.red "[Parsing Error]" ^ 
     (if infos <> Lexing.dummy_pos then
        Printf.sprintf " %s line %d, character %d : error when seeing token " 
          infos.pos_fname infos.pos_lnum 
          (1 + infos.pos_cnum - infos.pos_bol)
      else "")^ 
     token)


let send_error str infos = 
  InterpretationError 
    (Format.colorate Format.red "[Error]" ^ 
     (if infos <> Lexing.dummy_pos then
        Printf.sprintf " %s line %d, character %d : " 
          infos.pos_fname infos.pos_lnum 
          (1 + infos.pos_cnum - infos.pos_bol) 
      else  "") ^
     str)


(* an inference error can have three type:
   - a msg, which is a string. It is a final and fully treated error
   - a unification error if two types can't be unified
   *)
type inferrorinfo = 
  | Msg of string
  | UnificationError of string

exception InferenceError of inferrorinfo
let send_unification_error infos token = 
  InferenceError 
    (UnificationError 
       (Format.colorate Format.red "[Error]" ^ 
        (if infos <> Lexing.dummy_pos then 
           Printf.sprintf " %s line %d, character %d : " 
             infos.pos_fname 
             infos.pos_lnum 
             (1 + infos.pos_cnum - infos.pos_bol) 
         else "" ) ^
        token))

let send_inference_error infos token = 
  InferenceError 
    (Msg 
       (Format.colorate Format.red "[Error]" ^ 
        (if infos <> Lexing.dummy_pos then 
           Printf.sprintf " %s line %d, character %d : " 
             infos.pos_fname 
             infos.pos_lnum 
             (1 + infos.pos_cnum - infos.pos_bol)
         else "") ^
        token))


