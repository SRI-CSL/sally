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
  | IntegerRange of string

type sally_condition =
  | Equality of sally_condition * sally_condition
  | GreaterEqual of sally_condition * sally_condition
  | Greater of sally_condition * sally_condition
  | Or of sally_condition * sally_condition
  | And of sally_condition * sally_condition
  | Not of sally_condition
  | Add of sally_condition * sally_condition
  | Sub of sally_condition * sally_condition
  | Div of sally_condition * sally_condition
  | Mul of sally_condition * sally_condition
  | Value of string
  | Ident of string * sally_type
  | Ite of sally_condition * sally_condition * sally_condition
  | Forall of string * sally_type * sally_condition
  | Select of sally_condition * sally_condition
  | Exists of string * sally_type * sally_condition
  | True
  | False

type variable_declaration = string * sally_type

type state_type = state_type_identifier * (variable_declaration list)

type state = {
  id: state_identifier;
  state_type_id: state_type_identifier;
  condition: sally_condition;
}

type transition = {
  id: transition_identifier;
  state_type_id: state_type_identifier;
  formula: sally_condition;
}

type parametrized_type = string

type transition_system = {
  id: system_identifier;
  state_type: state_type;
  initial_state: state;
  transition: transition;
}

type query = {
  transition_system: transition_system;
  condition: sally_condition;
}

type context = {
  queries: query list;
  parametrized_types: parametrized_type list;
}

let and_ a b = And(a, b)
