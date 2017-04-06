



module Env =
     struct 
       module E = Map.Make(struct
           type t = string
          let compare = Pervasives.compare
        end)
       type ('a, 'b) t = {mem: 'a E.t; types: 'b E.t}

       let create = {mem = E.empty; types = E.empty}

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
           E.mem key map.mem
       let remove map key = 
           E.remove key map.mem
       let add map key prog =
         { map with mem = E.add key prog map.mem }
       let get_most_recent map key = 
           E.find key map.mem
       let add_type map key t =
         {map with types = E.add key t map.types}
       let get_type map key = 
         E.find key map.types
       end
