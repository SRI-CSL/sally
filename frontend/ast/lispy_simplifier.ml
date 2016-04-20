open Lispy_ast

let apply_to_condition f = function
	| Equality(a, b) -> Equality (f a, f b)
	| GreaterEqual(a, b) -> GreaterEqual(f a, f b)
	| Greater(a, b) -> Greater(f a, f b)
	| Or(a, b) -> Or(f a, f b)
	| And(a, b) -> And(f a, f b)
	| Not(a) -> Not(f a)
	| Add(a, b) -> Add(f a, f b)
	| Sub(a, b) -> Sub(f a, f b)
	| Div(a, b) -> Div(f a, f b)
	| Value(s) -> Value s
	| Ident(a, b) -> Ident(a, b)
	| Ite(a, b, c) -> Ite(f a, f b, f c)
	| Forall(a, b, c) -> Forall(a, b, f c)
	| Select(a, b) -> Select(f a, f b)
	| Exists(a, b, c) -> Exists(a, b, f c)
	| True -> True
	| False -> False

let rec simplify_condition = function
	| And(True, b) | And (b, True) -> simplify_condition b
	| Or(False, b) | Or (b, False) -> simplify_condition b
	| Or(a, b) ->
		let c = simplify_condition a
		and d = simplify_condition b in
		if c = False then d
		else if d = False then c
		else Or(c, d)
	| And(a, b) ->
		let c = simplify_condition a
		and d = simplify_condition b in
		if c = True then d
		else if d = True then c
		else And(c, d)
	| a -> apply_to_condition simplify_condition a

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
