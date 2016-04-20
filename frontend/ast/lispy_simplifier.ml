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

let simplify_transition (id, state_type_id, sally_condition) =
	id, state_type_id, simplify_condition sally_condition

let simplify_state (id, type_id, condition) =
	id, type_id, simplify_condition condition

let simplify_transition_system (system_identifier, state_type, initial_state, transition) =
	system_identifier, state_type, simplify_state initial_state, simplify_transition transition

let simplify_query (transition_system, sally_condition) =
	simplify_transition_system transition_system,
	simplify_condition sally_condition
