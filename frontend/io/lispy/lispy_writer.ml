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

(* Abstract syntax for the lispy style of the .mcmt files read by Sally *)

open Ast.Lispy_ast

type indentation = In | Out | None

let rec print_expr f =
	let print_folded s a b =
		Format.fprintf f "(%s  @[<v>" s;
		print_expr f a; Format.fprintf f " "; print_expr f b;
		Format.fprintf f "@])"
	in
	let print_folded3 s a b c =
		Format.fprintf f "@(%s@\n@[" s;
		print_expr f a; Format.fprintf f " ";
		print_expr f b; Format.fprintf f " ";
		print_expr f c;
		Format.fprintf f "@])"
	in
	function
	| Equality(a, b) -> print_folded "=" a b
	| Value(s) -> Format.fprintf f "%s" s
	| Ident(s) -> Format.fprintf f "%s" s
	| GreaterEqual(a, b) ->
		print_folded ">=" a b
	| Greater(a, b) ->
		print_folded ">" a b
	| Or(False, b) | Or (b, False) -> print_expr f b
	| Or(a, b) ->
		begin
		Format.fprintf f "(or @[<v>";
		let rec expand_or = function
		| Or(False, a) | Or(a, False) -> expand_or a
		| Or(c, d) ->
			begin
			expand_or c;
			Format.fprintf f "@;";
			expand_or d;
			end
		| a -> print_expr f a;
		in
		expand_or a;
		Format.fprintf f "@;";
		expand_or b;
		Format.fprintf f "@])";
		end
	| Add(a, b) ->
		print_folded "+" a b
	| And(True, b) | And (b, True) -> print_expr f b
	| And(a, b) ->
		begin
		Format.fprintf f "(and @[<v>";
		let rec expand_and = function
		| And(True, a) -> expand_and a
		| And(a, True) -> expand_and a
		| And(c, d) ->
			begin
			expand_and c;
			Format.fprintf f "@;";
			expand_and d;
			end
		| a -> print_expr f a
		in
		expand_and a;
		Format.fprintf f "@;";
		expand_and b;
		Format.fprintf f "@])";
		end
	| Ite(a, b, c) ->
		print_folded3 "ite" a b c
	| Not(a) ->
		begin
		Format.fprintf f "@[(not ";
		print_expr f a;
		Format.fprintf f ")@]";
		end
	| True -> Format.fprintf f "true"
	| False -> Format.fprintf f "false"

let print_transition f ((ident, state_type, sally_cond):transition) =
	Format.fprintf f "@[(define-transition %s state @;  " ident;
	print_expr f sally_cond;
	Format.fprintf f ")@]"

let print_state f ((ident, state_type, sally_cond):state) =
	Format.fprintf f "@[(define-states %s state @;  " ident;
	print_expr f sally_cond;
	Format.fprintf f ")@]"


let sally_type_to_string = function
	| Real -> "Real"
	| Bool -> "Bool"
	| Range(_, _) -> "Real"
	| Array(_, _) -> "Real"

let print_state_type f (ident, var_list) =
	Format.fprintf f "@[(define-state-type state @;  (@[<v>";
	let rec print_variable (name, sally_type) =
		match sally_type with
		| Array(Range(array_inf, array_sup), b) ->
			begin
			for i = array_inf to array_sup do
				print_variable (name ^ "!" ^ string_of_int i, b);
			done;
			end
		| _ ->
			Format.fprintf f "(%s %s)@\n" name (sally_type_to_string sally_type)
	in
	List.iter print_variable var_list;
	Format.fprintf f "@]))@]@\n"

let print_ts f (name, state_type, init, transition) =
	print_state_type f state_type;
	Format.fprintf f "@;";
	print_state f init;
	Format.fprintf f "@;";
	print_transition f transition;
	Format.fprintf f "@;";
	Format.fprintf f "(define-transition-system %s state init trans)" name

let print_query ch q =
	let f = Format.formatter_of_out_channel ch in
	let transition_system, cond = q in
	print_ts f transition_system;
	Format.fprintf f "@;@\n";
	Format.fprintf f "@[(query %s " (ts_name transition_system);
	print_expr f cond;
	Format.fprintf f "@])"
