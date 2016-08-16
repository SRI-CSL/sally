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

type mcmt_type = 
  | Real
  (* TODO: Integer *)
  | Bool
  | Array of mcmt_type * mcmt_type
  (* TODO: Predicate subtypes *)
  | Range of int * int
  | ProcessType of string
    
(** All MCMT expressions *)
type mcmt_expr =
  | Equality of mcmt_expr * mcmt_expr (** Equality t1 = t2 *)
  | GreaterEqual of mcmt_expr * mcmt_expr              
  | Greater of mcmt_expr * mcmt_expr
  (* TODO: maybe also <, <= *)
  | Or of mcmt_expr * mcmt_expr
  | And of mcmt_expr * mcmt_expr
  | Not of mcmt_expr
  | Add of mcmt_expr * mcmt_expr
  | Sub of mcmt_expr * mcmt_expr
  | Div of mcmt_expr * mcmt_expr
  | Mul of mcmt_expr * mcmt_expr
  | Value of string
  | LProc_cardinal of string (** #P: cardinality of a particular process type *)
  | Ident of string * mcmt_type
  | Ite of mcmt_expr * mcmt_expr * mcmt_expr
  | Forall of string * mcmt_type * mcmt_expr
  | Select of mcmt_expr * mcmt_expr
  | Store of mcmt_expr * mcmt_expr * mcmt_expr
  | Exists of string * mcmt_type * mcmt_expr
  | LSet_cardinal of string * mcmt_type * mcmt_expr (** # k: P such that F holds, with P process type and F formula *)
  | True
  | False

type variable_declaration = string * mcmt_type

type state_type = string * (variable_declaration list)

type state = {
  id: string;
  state_type_id: string;
  condition: mcmt_expr;
}

type transition = {
  id: string;
  state_type_id: string;
  formula: mcmt_expr;
}

type parametrized_type = string

type transition_system = {
  id: string;
  state_type: state_type;
  initial_state: state;
  transition: transition;
}

type query = {
  transition_system: transition_system;
  condition: mcmt_expr;
}
    
(** TODO: should just be a list of commands *)
type context = {
  queries: query list;
  parametrized_types: parametrized_type list;
}

let and_ a b = And(a, b)

(* Local Variables: *)
(* compile-command: "make -C ../../build/ -j 4" *)
(* caml-annot-dir: "../../build/frontend/ast/" *)
(* End: *)
