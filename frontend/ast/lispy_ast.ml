type state_identifier = string
type system_identifier = string
type state_type_identifier = string
type transition_identifier = string

type sally_type = 
	| Real
	| Bool
	| Array of sally_type * sally_type
	| Range of int * int

type sally_condition =
	| Equality of sally_condition * sally_condition
	| GreaterEqual of sally_condition * sally_condition
	| Greater of sally_condition * sally_condition
	| Or of sally_condition * sally_condition
	| And of sally_condition * sally_condition
	| Not of sally_condition
	| Add of sally_condition * sally_condition
	| Value of string
	| Ident of string
	| Ite of sally_condition * sally_condition * sally_condition
	| True
	| False

type variable_declaration = string * sally_type

type state_type = state_type_identifier * (variable_declaration list)

type state = state_identifier * state_type_identifier * sally_condition

type transition = transition_identifier * state_type_identifier * sally_condition

type transition_system = system_identifier * state_type * (* initial state *) state * transition

type query = transition_system * sally_condition

let ts_name (a, _, _, _) = a

type formatter = { ft: Format.formatter; mutable i: int }

