open Prettyprint
open Commons
open Expr
open Shared
open Errors
open Lexing


(* check wether a polymorphic type var is included in the type t 
   If this is the case, we are wanting to unify 'a something like 'a, which isn't good at all
*)
let occurs var t =
  let rec aux t =
	match t with
	| Types.Var x when !x = !var -> 
	  raise (InferenceError 
			   (Msg 
				  (Printf.sprintf "Unification error. Can't unify these two \
								   types: %s because one occurs in the other" 
					 (Types.print_duo (Types.Var var) t))))
	| Types.Var x -> 
	  begin
		(* this part is because variables are nested to a level: when seeing to variable
		   at different levels, the higher level one must be unyfied with the lower level one *)
		match !x with
		| Unbound (id', l') ->
		  let min_level = match !var with | Unbound(_, l) -> min l l' | _ -> l'
		  in x := Unbound (id', min_level)
		| Types.Link t -> aux t
	  end
	| Types.Fun (t1, t2) -> 
	  aux t1;aux t2
	| Types.Tuple l -> 
	  List.iter aux l
	| Types.Called (_, _, l) -> 
	  List.iter aux l
	| Types.Ref l -> aux l
	| Types.Array l -> aux l
	| Types.Constructor (_, l, Some l') -> 
	  aux l; aux l'
	| Types.Constructor (_, l, None) -> 
	  aux l
	| _ -> ()
  in aux t

(* instanciates a type, ie convert a type where all polymorphic types are fixed
   to a type where they can be changed 
   For use during unification
*)
let instanciate_with_tbl env tbl t level =
  let rec aux t =
	match t with 
	| Types.Constructor(name, a, Some b) -> 
	  Types.Constructor (name, aux a, Some (aux b))
	| Types.Constructor(name, a, None) -> 
	  Types.Constructor (name, aux a, None)
	| Types.Generic i -> 
    let _ = print_endline @@ "instanciating " ^ string_of_int i in
	  if Hashtbl.mem tbl i then
		Hashtbl.find tbl i
	  else
		let u = Types.new_var level
		in let _ = Hashtbl.add tbl i u
  in let Types.Var({contents = Unbound (x, _)}) = u
  in let _ = print_endline @@ "new instancing of " ^ string_of_int i ^  " at " ^ string_of_int x
		in u
	| Types.Var {contents = Types.Link x} -> 
	  aux x
	| Types.Fun (t1, t2) -> 
	  Types.Fun (aux t1, aux t2)
	| Types.Called(name, id, l) ->   
	  Env.get_corresponding_id env (Types.Called(name, id, List.map aux l))
	| Types.Tuple l -> 
	  Types.Tuple (List.map aux l)
	| Types.Ref l -> 
	  Types.Ref (aux l)
	| Types.Array l -> 
	  Types.Array (aux l)
	| t -> t
  in aux t

let instanciate env t level =
  let tbl = Hashtbl.create 0
  in instanciate_with_tbl env tbl t level

(* unify two types.
   Almost all of this function is straightforward, except for 
   the part when whe check if a variable occurs in a type. This
   must be done because unifying 'a with 'a is impossible
*)
let unify env level t1 t2 =
  let rec unify t1 t2 =
	if t1 == t2 then ()
	else match (t1, t2) with
	  | Types.Fun (a, b), Types.Fun (a', b') -> 
		unify a a'; unify b b'
	  | Types.Tuple l, Types.Tuple l' -> 
		List.iter2 unify l l'
	  | Types.Ref x, Types.Ref x' -> 
		unify x x'
	  | Types.Array x, Types.Array x' -> 
		unify x x'
	  | Types.Called(name, id, l), Types.Called(name', id', l') 
		when name = name' 
		  && (id < 0 || id' < 0 || id = id')
		  && List.length l = List.length l' -> 
		List.iter2 unify l l'

	  | Types.Constructor(name, l, None), Types.Constructor(name', l', None)  
		when snd name = snd name' ->
		unify l l'
	  | Types.Constructor(name, a, Some b), Types.Constructor(name', a', Some b') 
		when snd name = snd name' ->
		unify a a'; unify b b'
	  | Types.Var {contents = Types.Link t1}, t2
	  | t1, Types.Var {contents = Types.Link t2} -> 
		unify t1 t2
	  | Types.Var ({contents = Unbound _} as tv), t'
	  | t', Types.Var ({contents = Unbound _} as tv) -> 
		occurs tv t'; tv := Types.Link t'

	  (* here comes the most important part. We want user defined types to appear with their name.
		 So we cant return int when we unify a type test = int. Buf what happen if we must compare 
		 test with test2? Test2 might be declared as type test2 = test, so we must enroll it. 
		 But sometimes this could loop. For exemple, if test is a sum type, then getting the type affected to test in the env returns test. Everything here is made to avoid infinite loops *)
	  | y, (Types.Called (name, id, params) as x) 
	  | (Types.Called (name, id, params) as x), y ->
		let (x_type, x_repr) = begin try 
			Env.get_latest_userdef env name id params
		  with Not_found ->
			raise (send_inference_error 
					 Lexing.dummy_pos 
					 (Printf.sprintf "Type %s not found" 
						(string_of_ident name)))
		end
		in let x_repr = begin match x_repr with
			| Renamed_decl x -> 
			  x
			| Constructor_decl _ -> 
			  raise (InferenceError 
					   (UnificationError 
						  "Didn't wait for a constructor here"))
			| Module_sig_decl _ -> 
			  raise (InferenceError 
					   (UnificationError 
						  "Didn't wait for a module signature here"))
			| Sum_decl x -> 
			  begin match y with
				| Types.Called (name_t_y, id_t_y, params_t_y) -> 
				  let to_match = 
					snd @@ Env.get_latest_userdef env name_t_y id_t_y params_t_y
				  in begin match to_match with
					| Sum_decl _ -> 
					  (* in this case, we know that we will loop forever because the type are differents. We must stop *)
					  raise (InferenceError 
							   (UnificationError 
								  (Printf.sprintf "Can't unify type %s \
												   with type %s" 
									 (Types.print t1) 
									 (Types.print t2))))
					| _ ->  x
				  end
				| _ -> raise (InferenceError 
								(UnificationError 
								   "You encountered a case we can't infer"))
			  end 
		  end        
		in let tbl = Hashtbl.create 1
		in let (x_type, x_repr) = 
			 instanciate_with_tbl env tbl x_type level, 
			 instanciate_with_tbl env tbl x_repr level
		in let _ = unify x_type x
		in unify x_repr y
	  | _, _ ->
		raise (InferenceError 
				 (UnificationError 
					(Printf.sprintf 
					   "Can't unify type %s with type %s"
					   (Types.print t1)
					   (Types.print t2))))
  in unify t1 t2


(* generalize a type, ie convert a type where all polymorphic types can be changed
   to a type where they are fixed.
   For storage*)
let generalize t level = 
  let rec gen t =
	match t with
	| Types.Called (name, id, l) -> 
	  Types.Called (name, id, List.map gen l)
	| Types.Constructor(name, a, Some b) -> 
	  Types.Constructor (name, gen a, Some (gen b))
	| Types.Constructor(name, a, None) -> 
	  Types.Constructor (name, gen a, None)
	| Types.Var {contents = Unbound (name,l)} when l > level -> 
	  Types.Generic name
	| Types.Var {contents = Types.Link ty} -> 
	  gen ty
	| Types.Fun (t1, t2) -> 
	  Types.Fun  (gen t1, gen t2)
	| Types.Tuple l -> 
	  Types.Tuple (List.map gen l)
	(*we do not generalize refs!
	  | Types.Ref l -> Types.Ref (gen l)*)
	| Types.Array l -> 
	  Types.Array (gen l)
	| t -> t
  in gen t





(* deal with errors due to binary operators.
   It is a big chunk of code, it goes here in consequence *)
let binop_errors binop_type env (a, a_type) (b, b_type) symbol node error_infos =
  match binop_type with
  | Types.Fun (a_th_type, Types.Fun (b_th_type, _)) ->
	let _ = try
		unify env 0 a_th_type a_type 
	  with InferenceError (UnificationError _) ->
		let msg = 
		  Printf.sprintf 
			"Operator %s, left argument: can't match type %s with type %s\n    \
 in expression: %s" 
			(symbol) 
			(Types.print b_th_type) 
			(Types.print b_type) 
			(print_binop node "                 " true false)
		in raise (send_inference_error error_infos msg)
	in let _ = try
		   unify env 0 b_th_type b_type
		 with InferenceError (UnificationError _) ->
		   let msg = 
			 Printf.sprintf "Operator %s, right argument: can't match type %s\
 with type %s\n    in expression: %s" 
			   (symbol) 
			   (Types.print b_th_type) 
			   (Types.print b_type) 
			   (print_binop node "                 " false true)
		   in raise (send_inference_error error_infos msg)
	in raise (InferenceError 
				(Msg ("a boolean operator was coded in wrong format")))
  | _ -> raise (send_inference_error error_infos "This binary op didnt'
 have a correct type")





let get_constructor_definition env name error_infos level =   
  try    
	let _, x = Env.get_latest_userdef env name (-1) [] in
	let x = match x with
	  | Constructor_decl x -> 
		x
	  | _ -> 
		raise (send_inference_error error_infos "constructor not defined")
	in instanciate env x level 
  with Not_found -> 
	raise (send_inference_error 
			 error_infos 
			 (Printf.sprintf "Constructor %s not defined" 
				(string_of_ident name))) 

(* get the type of a constructor *)
let get_constructor_type env name error_infos level =
  match (get_constructor_definition env name error_infos level) with  
  | Types.Constructor (_, a, Some _) -> a  
  | Types.Constructor (_, a, None) -> a   | _ -> 
	failwith "how am I supposed to get the type of a constructor if 
I don't have a constructor?" 


(* compute the type of (and check inference)
   of a pattern.
   It also allocates the types of symboles
   (for exemple, in the pattern (x, 2, y) it will
   allocates the type of x and y)
*)
let rec type_pattern_matching expr t level env = 
  match expr with
  | Underscore -> 
	env
  | Ident (name, _) -> 
	let new_type = generalize t level
	in Env.add_type env name new_type
  | FixedType (x, t', error) -> 
	begin
	  try
		let t' = instanciate env t' level in
		let env = type_pattern_matching x t' level env
		in let _ = unify env level t t'
		in env
	  with InferenceError (UnificationError m) ->
		raise (send_inference_error error m)
	end
  | Const _ -> 
	unify env level Types.Int t; env
  | Bool _ -> 
	unify env level Types.Bool t; env
  | Unit -> 
	unify env level Types.Unit t; env
  | Tuple (l, _) ->
	let new_types = List.map (fun _ -> Types.new_var level) l
	in let _ = unify env level (Types.Tuple new_types) t
	in let rec aux l l_types env =
		 match (l, l_types) with 
		 | [], [] -> 
		   env
		 | x::l, x_type::l' -> 
		   aux l l' @@ type_pattern_matching x x_type level env
		 | _ -> failwith "this wasn't suppose to happen"
	in aux l new_types env
  | Constructor (name, None, error_infos) ->
	unify env level (get_constructor_type env name error_infos level) t;
	env
  | Constructor (name, Some expr, error_infos) ->
	let constructeur = get_constructor_definition env name error_infos level
	in begin match constructeur with
	  | Types.Constructor (_, arg, Some type_expr) ->
		let _ = unify env level t arg
		in type_pattern_matching expr type_expr level env
	  | _ -> 
		failwith "ouspi"
	end
  | _ -> failwith "incorrect symbol encountered during pattern matching"






let rec update_constraints t env = 
  let tbl = Hashtbl.create 0 in
  let rec aux t level = 
    let aux_s = fun t -> aux t level in
  match t with
  | FixedType(expr, t_expr, er) -> 
    FixedType (aux expr level, instanciate_with_tbl env tbl t_expr level , er)
  | Constructor(i, None, er) -> t
  | Ident _ -> t
  | Constructor(i, Some e, er) -> 
    Constructor(i, Some (aux e level), er)
  | ArrayItem(a, b, er) ->
    ArrayItem(aux_s a, aux_s b, er)
  | ArraySet(a, b, c, er) ->
    ArraySet(aux_s a, aux_s b, aux_s c, er) 
  | MainSeq(a, b, er) ->
    MainSeq(aux_s a, aux_s b, er)
  | Seq(a, b, er) ->
    Seq(aux_s a, aux_s b, er)
  | Not (a, er) ->
    Not (aux_s a, er)
  | In(a, b, er) ->
    In(aux_s a, aux_s b, er)
  | Let (a, b, er) ->
    Let(aux_s a, aux_s b, er)
  | LetRec (a, b, er) ->
    LetRec(aux_s a, aux_s b, er)
  | Call(a, b, er) ->
    Call(aux_s a, aux_s b, er)
  | TryWith(a, b, c, er) ->
    TryWith(aux_s a, aux_s b, aux_s c, er) 
  | Raise(a, er) ->
    Raise (aux_s a, er)
  | Bang(a, er) ->
    Bang (aux_s a, er)
  | Ref(a, er) ->
    Ref(aux_s a, er)
  | IfThenElse(a, b, c, er) ->
    IfThenElse(aux_s a, aux_s b, aux_s c, er) 
  | RefLet (a, b, er) ->
    RefLet(aux_s a, aux_s b, er)
  | Fun (a, b, er) ->
    Fun(aux_s a, aux_s b, er)
  | Printin(a, er) ->
    Printin(aux_s a, er)
  | ArrayMake(a, er) ->
    ArrayMake(aux_s a, er)
  | BinOp(s, a, b, er) ->
    BinOp(s, aux_s a, aux_s b, er)
  | Tuple(l, er) ->
    Tuple(List.map aux_s l, er)
  | MatchWith(p, l, er) ->
    MatchWith(aux_s p, List.map(fun (a, b) -> (aux_s a, aux_s b)) l, er)
  | Module (name, expr, b, er) ->
    Module(name, List.map aux_s expr, b, er)
  | t -> t
  in aux t 0










(* the type inference itself.
   It is just some boring steps using previous functions
   The code is horrific because we are also checking for
   errors
*)
let analyse expr env = 
  let rec inference expr env level =
	let e, t = match expr with
	  | Const _ -> 
		env, Types.Int

	  | Bool _ -> 
		env, Types.Bool

	  | Unit -> 
		env, Types.Unit

	  | Underscore ->
		env, Types.new_var level

	  | FixedType (x, t', error) -> 
		begin
		  try
			let t' = instanciate env t' level
			in let env, t = inference x env level
			in let _ = unify env level t t'
			in env, t'
		  with InferenceError (UnificationError m) ->
			raise (send_inference_error error m)
		end

	  | Ident(name, error_infos) ->
		begin
		  try
			env, instanciate env (Env.get_type env name) level
		  with Not_found ->
			raise (send_inference_error 
					 error_infos 
					 ("identifier '" ^ string_of_ident name ^ "' not found"))
		end

	  | Constructor (name, None, error_infos) ->
		let def = get_constructor_definition env name error_infos level
		in begin
		  try
			let u = Types.new_var level 
			in let _ = unify env level (Types.Constructor(name, u, None)) def
			in env, u
		  with InferenceError (UnificationError m)->
			begin
			  match def with
			  | Types.Constructor (_, _, Some l) ->
				raise (send_inference_error 
						 error_infos 
						 "expected a constructor with arguments")
			  | _ ->
				raise (send_inference_error error_infos m) 
			end
		end

	  | Constructor(name, Some arg, error_infos) 
	  | Call(Constructor (name, None, _), arg, error_infos) ->
		let def = get_constructor_definition env name error_infos level
		in let _, t_arg = inference arg env level
		in begin
		  try
			let u = Types.new_var level
			in let _ = unify env level 
				   (Types.Constructor(name, u, Some t_arg)) 
				   def 
			in env, u
		  with InferenceError (UnificationError m)->
			begin
			  match def with
			  | Types.Constructor (_, _, None) ->
				raise (send_inference_error 
						 error_infos 
						 "expected a constructor without arguments")
			  | Types.Constructor (_, _, Some l) ->
				raise (send_inference_error 
						 error_infos 
						 (Printf.sprintf "argument was expected to have type %s\
 but had type %s"
							(Types.print l) 
							(Types.print t_arg)))
			  | _ -> failwith "bad type"
			end
		end


	  | TypeDecl (id, l, error_infos) ->
		Env.add_userdef env expr, Types.Unit

	  | Tuple (l, _) ->
		env, Types.Tuple (List.map (fun x -> snd (inference x env level)) l)

	  | Let(pattern, expr, _) ->
		let type_expr = snd @@ inference expr env (level + 1)
		in type_pattern_matching pattern type_expr level env, 
		   instanciate env type_expr level

	  | LetRec((Ident (name, _)), expr, _) ->
		let env' = Env.add_type env name ((Types.new_var (level+1)))
		in let type_expr = snd @@ inference expr env' (level + 1)
		in let _ = unify env level type_expr ((Env.get_type env' name))
		in let env'' = Env.add_type env' name (generalize type_expr level)
		in env'', Env.get_type env'' name

	  | In(Let(pattern, expr, _), next, _) ->
		let type_expr = snd @@ inference expr env (level + 1)
		in inference next 
		  (type_pattern_matching pattern type_expr level env) 
		  level

	  | In(LetRec((Ident (name, _)), expr, _), next, _) ->
		let env' = Env.add_type env name (Types.new_var (level+1))
		in let type_expr = snd @@ inference expr env' (level + 1)
		in let _ = unify env level type_expr (Env.get_type env' name)
		in let env'' = Env.add_type env' name (generalize (type_expr) level)
		in inference next env'' level

	  | IfThenElse(cond, if_expr, else_expr, error_infos) ->
		let _, cond_type = inference cond env level
		in let _ = try unify env level cond_type Types.Bool
			 with InferenceError (UnificationError _) ->
			   raise (send_inference_error 
						error_infos 
						(Printf.sprintf "A condition must have type bool,\
here it is having type %s" 
						   (Types.print cond_type)))
		in let _, if_expr_type = inference if_expr env level
		in let _, else_expr_type = inference else_expr env level
		in let _ = try 
			   unify env level if_expr_type else_expr_type
			 with InferenceError (UnificationError m) ->
			   raise (send_inference_error error_infos m)
		in env, if_expr_type


	  | Fun(args, expr, error_infos) ->
		let args_type = Types.new_var level
		in let env' = type_pattern_matching args args_type level env
		in let _, out_type = inference expr env' level
		in env, Types.Fun (args_type, out_type)

	  | Call(expr, arg, error_infos) ->
		let _, fun_type = inference expr env level
		in let _, arg_type = inference arg env level
		in let out_type = Types.new_var level
		in begin try
			let _ = unify env level fun_type (Types.Fun (arg_type, out_type))
			in env, out_type
		  with InferenceError (UnificationError m) ->
		  match fun_type with
		  | Types.Fun (arg_th_type, _) -> 
			raise (send_inference_error
					 error_infos 
					 (Printf.sprintf 
						"function as argument of type %s, but here it is called\
 with type %s" 
						(Types.print arg_th_type) 
						(Types.print arg_type)))
		  | _ -> 
			raise (send_inference_error
					 error_infos 
					 (Printf.sprintf 
						"Calling function with too much arguments: %s %s"
						m 
						(pretty_print expr)))
		end

	  | BinOp(x, a, b, t) ->
		let _, b_type = inference b env level
		in let _, a_type = inference a env level
		in let comp_type = instanciate env (x#type_check) level
		in let out_type = Types.new_var level
		in begin try
			let _ = unify env level comp_type 
				(Types.Fun(a_type, Types.Fun (b_type, out_type)))
			in env, out_type
		  with InferenceError (UnificationError _) ->
			binop_errors comp_type env (a, a_type) (b, b_type) x#symbol expr t
		end

	  | Seq(a, b, _) | MainSeq(a, b, _) ->
		let env', _ = inference a env level
		in inference b env' level

	  | MatchWith (match_expr, matches, errors) ->
		let _, match_expr_type = inference match_expr env level
		in let temp = List.map (fun (m, a) -> 
			let env' = type_pattern_matching m match_expr_type level env
			in match_expr_type, snd @@ inference a env' level)
			matches
		in let pattern_types, action_types = List.split temp
		in let _ = List.fold_left (fun a b -> begin
			  try
				unify env level a b;b
			  with InferenceError (UnificationError _)->
				raise (send_inference_error 
						 errors 
						 (Printf.sprintf 
							"can't unify env level %s and %s in pattern matching"
							(Types.print a)
							(Types.print b)))   
			end) 
			match_expr_type 
			pattern_types
		in env, List.fold_left (fun a b -> begin
			  try
				unify env level a b;b
			  with InferenceError (UnificationError _) ->
				raise (send_inference_error errors 
						 (Printf.sprintf 
							"Can't unify env level expressions in matching.\
Should it return %s or %s?" 
							(Types.print a)
							(Types.print b)))
			end )
			(List.hd action_types) 
			(List.tl action_types)

	  | Raise (e, error_infos) ->
		let _, t = inference e env level
		in let _ = unify env level t Types.Int
		in env, (Types.new_var (level))

	  | TryWith (try_clause, error, with_clause, error_infos) ->
		let _, type_try = inference try_clause env level
		in let env' = begin try
			   type_pattern_matching error Types.Int level env
			 with InferenceError (UnificationError m) ->
			   raise (send_inference_error error_infos m)
		   end
		in let _, type_with = inference with_clause env' level
		in let _ = begin try
			   unify env level type_try type_with
			 with InferenceError  (UnificationError m)->
			   raise (send_inference_error 
						error_infos 
						(Printf.sprintf "The two expression in a trywith clause\
 must have the same type. Here: \n  First expression has type %s\n \
Second expression has type %s" 
						   (Types.print type_try) 
						   (Types.print type_with)))
		   end 
		in env, type_try


	  | Ref (x, error_infos) ->
		let _, t = inference x env level
		in env, Types.Ref t

	  | Bang (x, error_infos) ->
		let _, t = inference x env level
		in let n = Types.new_var level
		in let _ = unify env level t (Types.Ref n)
		in env, n

	  | ArraySet (id, expr, nvalue, error_infos) ->
		let _, th = inference (ArrayItem(id, expr, error_infos)) env level
		in let _, tvalue = inference nvalue env level
		in let _ = begin try 
			   unify env level th tvalue 
			 with InferenceError (UnificationError _) ->
			   raise (send_inference_error 
						error_infos 
						(Printf.sprintf "Can't affect an expression of type %s\
to an element of a %s.\n  In expression: %s" 
						   (Types.print tvalue) 
						   (Types.print th) 
						   (pretty_print_arrayset expr "" true true)))
		   end 
		in env, Types.Unit

	  | ArrayItem (id, expr, error_infos) ->
		let u = Types.new_var level
		in let _ = begin try 
			   unify env level (Types.Array u) (snd @@ inference id env level)
			 with InferenceError (UnificationError _ ) ->
			   raise (send_inference_error 
						error_infos 
						(Printf.sprintf "expression %s is not representing \
an array" 
						   (pretty_print_arrayitem expr "" true true false)))
		   end 
		in let _ =  begin try 
			   unify env level u (snd @@ inference expr env level)
			 with InferenceError (UnificationError _ ) ->
			   raise (send_inference_error
						error_infos 
						(Printf.sprintf "Can't suscribe to the array. The index\
isn't an int.\n  In expression: %s" 
						   (pretty_print_arrayitem expr "" true false true)))
		   end in
		env, u



	  (* now the buildins - printin, not, amake, .... *)
	  | ArrayMake (expr, t) -> begin
		  let _, arg_type = inference expr env level
		  in try
			let _ = unify env level arg_type Types.Int
			in env, Types.Array Types.Int
		  with InferenceError (UnificationError m) ->
			raise (send_inference_error 
					 t 
					 (Printf.sprintf "aMake constructor requires a int\
 argument, not a %s.\n  In expression: %s" 
						(Types.print arg_type) 
						(pretty_print_amake expr "  " true true)))
		end
	  | Not (expr, t) -> begin
		  let _, arg_type = inference expr env level
		  in try
			let _ = unify env level arg_type Types.Bool
			in env, Types.Bool
		  with InferenceError (UnificationError m) ->
			raise (send_inference_error 
					 t 
					 (Printf.sprintf "Not function requires a bool argument,\
 not a %s.\n  In expression: %s" 
						(Types.print arg_type) 
						(pretty_print_amake expr "  " true true)))
		end

	  | Printin (expr, t) -> begin
		  let _, arg_type = inference expr env level
		  in try
			let _ = unify env level arg_type Types.Int
			in env, Types.Int
		  with InferenceError (UnificationError m) ->
			raise (send_inference_error 
					 t 
					 (Printf.sprintf "prInt constructor requires a int \
argument, not a %s.\n  In expression: %s" 
						(Types.print arg_type) 
						(pretty_print_prInt expr "  " true true)))
		end

	  | Module _ -> env, Types.Unit
	  | _ -> failwith @@ "Encoutered something we can't infer:" ^ show_expr expr
	in e, t
  in inference expr env 0
