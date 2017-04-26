type 'a fix = Buildins_Fix of ('a fix -> 'a);;
let buildins_y t = let p (Buildins_Fix f) x = t (f (Buildins_Fix f)) x in p (Buildins_Fix p);;



    let buildins_y = fun temp_k -> 
      fun temp_kE -> 
        temp_k (fun t -> 
          fun temp_k -> 
            fun temp_kE -> 
              (fun temp_k -> 
                fun temp_kE -> 
                  temp_k (fun (Buildins_Fix f) -> 
                    fun temp_k -> 
                      fun temp_kE -> 
                        temp_k (fun x -> 
                          fun temp_k -> 
                            fun temp_kE -> 
                              (fun temp_k -> 
                                fun temp_kE -> 
                                  temp_k x) (fun temp_v2 -> 
                                (fun temp_k -> 
                                  fun temp_kE -> 
                                    (fun temp_k -> 
                                      fun temp_kE -> 
                                        (fun temp_k -> 
                                          fun temp_kE -> 
                                            (fun temp_k -> 
                                              fun temp_kE -> 
                                                temp_k f) (fun temp_e -> 
                                              temp_k (Buildins_Fix temp_e)) temp_kE) (fun temp_v2 -> 
                                          (fun temp_k -> 
                                            fun temp_kE -> 
                                              temp_k f) (fun temp_f -> 
                                            temp_f temp_v2 temp_k temp_kE) temp_kE) temp_kE) (fun temp_v2 -> 
                                      (fun temp_k -> 
                                        fun temp_kE -> 
                                          temp_k t) (fun temp_f -> 
                                        temp_f temp_v2 temp_k temp_kE) temp_kE) temp_kE) (fun temp_f -> 
                                  temp_f temp_v2 temp_k temp_kE) temp_kE) temp_kE))) (fun p -> 
                (fun temp_k -> 
                  fun temp_kE -> 
                    (fun temp_k -> 
                      fun temp_kE -> 
                        (fun temp_k -> 
                          fun temp_kE -> 
                            temp_k p) (fun temp_e -> 
                          temp_k (Buildins_Fix temp_e)) temp_kE) (fun temp_v2 -> 
                      (fun temp_k -> 
                        fun temp_kE -> 
                          temp_k p) (fun temp_f -> 
                            temp_f temp_v2 temp_k temp_kE) temp_kE) temp_kE) temp_k temp_kE) temp_kE);;

let buildins_y_noinference t = let p f x = t (f f) x in p p;;
