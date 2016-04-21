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

let simplify_condition = apply_to_condition identity_pass

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


