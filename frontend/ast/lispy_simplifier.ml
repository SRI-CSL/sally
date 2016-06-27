open Lispy_ast

type pass = sally_condition -> sally_condition

let (>>) f g x = g @@ f @@ x

let rec apply_to_condition g c =
	let f = apply_to_condition g in
	match c with
	| Equality(a, b) 		-> g @@ Equality (f a, f b)
	| GreaterEqual(a, b) 	-> g @@ GreaterEqual(f a, f b)
	| Greater(a, b) 		-> g @@ Greater(f a, f b)
	| Or(a, b) 				-> g @@ Or(f a, f b)
	| And(a, b) 			-> g @@ And(f a, f b)
	| Not(a) 				-> g @@ Not(f a)
	| Add(a, b) 			-> g @@ Add(f a, f b)
	| Sub(a, b) 			-> g @@ Sub(f a, f b)
	| Div(a, b) 			-> g @@ Div(f a, f b)
	| Value(s) 				-> g @@ Value s
	| Ident(a, b) 			-> g @@ Ident(a, b)
	| Ite(a, b, c) 			-> g @@ Ite(f a, f b, f c)
	| Forall(a, b, c) 		-> g @@ Forall(a, b, f c)
	| Select(a, b) 			-> g @@ Select(f a, f b)
	| Exists(a, b, c) 		-> g @@ Exists(a, b, f c)
	| True -> True
	| False -> False

let identity_pass = function
	| And(True, b) | And (b, True)
	| Or(False, b) | Or (b, False)
	| Not(Not(b)) -> b
	| a -> a

(** A first binded existential variable is a variable which is bound at the top
	of the condition tree (or that has only existential parents) *)
let rec get_first_exist_binded_variables = function
	| Exists(a, t, c) -> (a,t) :: get_first_exist_binded_variables c
	| a -> []

let rec list_inter a b compare =
	let a = List.sort compare a
	and b = List.sort compare b in
	let rec list_inter_aux = function
	| (t1::q1, t2::q2) ->
		let comp = compare t1 t2 in
		if comp > 0 then
			list_inter_aux (q1, (t2::q2))
		else if comp < 0 then
			list_inter_aux ((t1::q1), q2)
		else (t1, t2) :: (list_inter_aux (q1, q2))
	| ([], _) -> []
	| (_, []) -> []
	in
	list_inter_aux (a, b)

let rec remove_first_existentials b l =
	match b with
	| Exists(n, t, c) ->
		let c = remove_first_existentials c l in
		if List.exists (fun ((name, _), _) -> name = n) l then
			c
		else
			Exists(n, t, c)
	| a ->
		let renaming = List.fold_left (fun p ((name, _), (subst_name, _)) ->
			p >> begin function
			| Ident(s, mytype) when s = name -> Ident(subst_name, mytype)
			| a -> a
			end
		) (fun x -> x) l in
		apply_to_condition renaming a

let existential_pass = function
	| Or(a, b) ->
		(* This code is not optimal, let's keep in mind that the existential
		   variable list has probably a length < 4 (anyway, if it is too long
		   there will be a huge bottleneck in the solver), so we can have a few
		   extra split, combine, sort on those lists *)
		let a_variables = get_first_exist_binded_variables a
		and b_variables = get_first_exist_binded_variables b
		in
		let inter_a, inter_b =
			list_inter a_variables b_variables ( fun a b ->
				compare (snd a) (snd b))
			|> List.split
		in
		let new_vars =
			List.combine inter_a inter_b
			|> List.map (fun ((na, t), (nb, b)) ->
				if na = nb then na, t
				else Lispy_var.get_fresh_variable (), t)
		in
		let a =
			List.combine inter_a new_vars
			|> remove_first_existentials a
		and b =
			List.combine inter_b new_vars
			|> remove_first_existentials b
		in
		List.fold_left (fun c (var, var_type) ->
			Exists(var, var_type, c)) (Or(a, b)) new_vars
	| a -> a

let simplify_condition = apply_to_condition (identity_pass >> existential_pass)

let simplify_transition t =
	{ t with formula = simplify_condition t.formula; }

let simplify_state (s:state) =
	{ s with condition = simplify_condition s.condition; }

let simplify_transition_system transition_system  =
	{ transition_system with
	  initial_state = simplify_state transition_system.initial_state;
	  transition = simplify_transition transition_system.transition; }

let simplify_query q =
	{ transition_system = simplify_transition_system q.transition_system;
	  condition = simplify_condition q.condition; }

let simplify_context c =
	{ c with queries = List.map simplify_query c.queries }


(* Local Variables: *)
(* compile-command: "make -C ../../build/" *)
(* End: *)
