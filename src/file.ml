open Commons

(* max search depth *)
let search_max_depth = ref 4

(* check if a file is hidden *)
let is_hidden file_name =
  String.length file_name >= 1 && file_name.[0] = '.'

(* concat two paths together *)
let concat p f = p ^ "/" ^ f

type result = None | Found of string

(* explode a file name in a tuple (name, extension) *)
let explode_file file_name =
  let count = ref 0 
  in let _ = String.iter (fun c -> if c = '.' then incr count) file_name
  in match !count with
  | 1 -> let pos = String.index file_name '.' 
    in (String.sub file_name 0 pos,
        String.sub file_name (pos+1) (String.length file_name - pos - 1))
  | _ -> ("", "")



let get_visible path obj_list =
  List.filter 
    (fun a -> not (is_hidden a)) 
    obj_list
let get_explorable_folders path obj_list =
  List.filter 
    (fun n -> Sys.is_directory (concat path n)) 
    obj_list
let get_fouine_files path obj_list = 
  List.filter 
    (fun n -> 
       if Sys.is_directory (concat path n) then 
         false 
       else 
         let (a, e) = explode_file n in e = "fo") 
    obj_list


(* explore until we have found a file named target or reached a depth superior
   to the max depth allowed *)
let rec explore target path depth =
  let rec aux fifo = 
    match fifo with
    | [] -> None
    | (path, depth)::tl when depth > !search_max_depth -> None
    | (path, depth)::tl ->
      let files = list_of_array @@ Sys.readdir path
      in let files = get_visible path files
      in let folders = get_explorable_folders path files
      in let fouine = get_fouine_files path files
      in begin try
          Found (concat path 
                   (List.find 
                      (fun name ->
                         let name = String.uncapitalize_ascii name 
                         in let (name, _) = explode_file name
                         in name = target)
                      fouine))
        with Not_found -> 
          aux (tl @ List.map (fun a -> (concat path a, depth+1)) folders)
      end
  in aux [(".", 0)]


let rec seek_module name =
  let result = explore (String.uncapitalize_ascii name) "." 0
  in match result with
  | Found p -> p
  | _ -> raise Not_found


