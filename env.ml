open Expr

module Env =
     struct 
       module E = Map.Make(struct
           type t = string
          let compare = Pervasives.compare
        end)
       type t = expr list E.t

       let add map key prog = 
            if E.mem key map then
              let e = E.find key map
              in E.add key (prog :: e) map
            else 
              E.add key [prog] map


       let get_most_recent map key = 
            if E.mem key map then
              List.hd @@ E.find key map
            else 
              failwith "identifier not found"

       end
