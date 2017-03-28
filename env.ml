module Env =
     struct 
       module E = Map.Make(struct
           type t = string
          let compare = Pervasives.compare
        end)
       type 'a t = 'a E.t

       let create = E.empty

       (*let add map key prog = 
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
        *)
       let add map key prog =
         E.add key prog map
       let get_most_recent map key = 
         try 
           E.find key map 
         with Not_found ->
           failwith @@ "identifier "^key^" not found"
       end
