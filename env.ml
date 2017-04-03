



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
       let mem map key =
           E.mem key map
       let remove map key = 
           E.remove key map
       let add map key prog =
         E.add key prog map
       let get_most_recent map key = 
           E.find key map 
       end
