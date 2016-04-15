(*
 * This file is part of sally.
 * Copyright (C) 2016 SRI International.
 *
 * Sally is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Sally is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with sally.  If not, see <http://www.gnu.org/licenses/>.
 *)

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
	| Ident of string * sally_type
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

