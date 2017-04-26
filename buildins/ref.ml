type 'a list = Buildins_None_List | Buildins_Elt_List of 'a * 'a list;;
type 'a ref_type = Ref of 'a;;

let buildins_allocate v env =
  let (x, env) = env
  in (Ref x, (x+1, Buildins_Elt_List ((x, v), env)));;

let buildins_read v env =
  let Ref v = v in 
  let (x, env) = env in
  let rec aux l =
    match l with
    | Buildins_None_List -> raise 0
    | Buildins_Elt_List ((r, w), tl) ->
      if r = v then 
        w
        else 
          aux tl
  in (aux env);;


let buildins_modify env (re, value)=
  let Ref re = re in 
  let (x, env) = env in
  let rec aux l =
    match l with
    | Buildins_None_List -> l
    | Buildins_Elt_List ((r, w), tl) ->
      if r=re  then 
        Buildins_Elt_List((r, value), aux tl)
      else 
        Buildins_Elt_List((r, w), aux tl)
          
  in (x, aux env);;

let buildins_create = (0, Buildins_None_List);;
