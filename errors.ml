open Lexing

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

exception InterpretationError of string
let send_error str infos = 
  InterpretationError (colorate red "[Error]" ^ Printf.sprintf " line %d, character %d : %s" infos.pos_lnum (1 + infos.pos_cnum - infos.pos_bol) str)

