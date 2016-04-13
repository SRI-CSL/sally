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

open Ast
open Ast.Lispy_ast
open Ast.Sal_ast

exception Not_implemented

module StrMap = Map.Make(String)

type sally_substitution =
	Expr of sally_condition * sally_type
	| Fun of (string * sally_type) list * sal_expr
	| Type of sally_type

type sally_context = sally_substitution StrMap.t

exception CannotUseFunctionAsExpression
exception CannotUseExpressionAsFunction of string

let ctx_union a b =
	StrMap.fold (fun k v c -> StrMap.add k v c) a b

let eval_sally ctx = function
	| Value(s) -> s

let eval_sal ctx = function
	| Decimal(i) -> Value (string_of_int i)
	| Float(i) -> Value(string_of_float i)

	| Ident(s) -> (match StrMap.find s ctx with
		| Expr(s, _) -> Value(eval_sally ctx s)
		| _ -> raise CannotUseFunctionAsExpression)
	| _ -> failwith "couldn't statically evaluate"

exception UnknownType of string

let rec sal_type_to_sally_type ctx = function
	| Base_type("NATURAL") -> Real
	| Base_type("BOOLEAN") -> Bool
	| Base_type("REAL") -> Real
	| Base_type(e) -> (match StrMap.find e ctx with
		| Type(t) -> t
		| _ -> raise (UnknownType(e))
		)
	| Array(t1, t2) -> Lispy_ast.Array(sal_type_to_sally_type ctx t1, sal_type_to_sally_type ctx t2)
	| Enum(l) -> Real
	| Subtype(_) -> Real
	| Range(i1, i2) ->
		match eval_sal ctx i1, eval_sal ctx i2 with
		| Value(a), Value(b) -> Lispy_ast.Range (int_of_string a, int_of_string b)
		| _ -> failwith "couldn't evaluate properly"

let sal_state_vars_to_state_type (ctx:sally_context) name vars =
	let sally_vars = List.(concat @@ map (fun (_, declarations) ->
		concat @@ map (fun (ids, ty) ->
		let t = sal_type_to_sally_type ctx ty in
		map (fun n -> n, t) ids) declarations) vars) in

	let type_init_ctx = List.fold_left
		(fun ctx (n, t) ->
			StrMap.add n (Expr (Lispy_ast.Ident(n), t)) ctx
		) ctx sally_vars in

	let transition_ctx = List.fold_left
		(fun ctx (n, t) ->
			let ctx = StrMap.add n (Expr(Lispy_ast.Ident ("state."^n), t)) ctx in
			StrMap.add (n^"'") (Expr(Lispy_ast.Ident("next."^n), t)) ctx
		) ctx sally_vars in

	type_init_ctx, transition_ctx, ((name, sally_vars):state_type)

exception InadequateArrayUse

let rec sal_expr_to_lisp (ctx:sally_context) = function
	| Decimal(i) -> Value (string_of_int i)
	| Float(i) -> Value(string_of_float i)

	| Ident(s) -> (match StrMap.find s ctx with
		| Expr(s, _) -> s
		| _ -> raise CannotUseFunctionAsExpression)

	| Eq(a, b) -> Equality(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)
	| Ge(a, b) -> GreaterEqual(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)
	| Gt(a, b) -> Greater(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)
	| Lt(a, b) -> Greater(sal_expr_to_lisp ctx b, sal_expr_to_lisp ctx a)
	| Le(a, b) -> GreaterEqual(sal_expr_to_lisp ctx b, sal_expr_to_lisp ctx a)
	| Implies(a, b) -> Or(Not(sal_expr_to_lisp ctx a), sal_expr_to_lisp ctx b)
	| Add(a, b) -> Lispy_ast.Add(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)

	| Next(s) -> (failwith ("Next ? " ^ s))

	| Funcall("G", [l]) -> sal_expr_to_lisp ctx l
	| Funcall(name, args_expr) -> (match  StrMap.find name ctx with
		| Fun(decls, expr) ->
			let args = List.combine decls (List.map (sal_expr_to_lisp ctx) args_expr) in
			let inside_function_ctx = List.fold_left (fun ctx ((arg_name, arg_type), arg_value) ->
				StrMap.add arg_name (Expr(arg_value, arg_type)) ctx) ctx args in
			sal_expr_to_lisp inside_function_ctx expr
		| _ -> raise (CannotUseExpressionAsFunction name)
		)

	| Cond([], else_term) -> sal_expr_to_lisp ctx else_term
	| Cond((a,b)::q, else_term) ->
		let a = sal_expr_to_lisp ctx a in
		let b = sal_expr_to_lisp ctx b in
		let next_condition = Cond(q, else_term) in
		Ite(a, b, sal_expr_to_lisp ctx next_condition)
	
	| Array_access(a, b) ->
		let sally_a = sal_expr_to_lisp ctx a in
		let sally_b = sal_expr_to_lisp ctx b in
		(match sally_a, sally_b with
		| Ident(sa), Value(sb) ->
			Ident(sa ^ "!" ^ sb)
		| _ -> raise InadequateArrayUse
		)
	| Set_literal(_) -> failwith "set"
	| Array_literal(n, e, e2) -> (failwith "Unsupported Array_literal")
	| Cond(_) -> failwith "cond"
	| Forall(t::q, expr) ->
		begin
		match t with
		| [], sal_type -> sal_expr_to_lisp ctx (Forall(q, expr))
		| t::end_decl, sal_type ->
			let sally_type = sal_type_to_sally_type ctx sal_type in
			match sally_type with
			| Range(a, b) ->
				let cond = ref True in
				let _ = for i = a to b do
					let (tmp_ctx:sally_context) = StrMap.add t (Expr(Value(string_of_int i), Real)) ctx in
					cond := Lispy_ast.And(!cond, sal_expr_to_lisp tmp_ctx (Forall((end_decl, sal_type)::q, expr)))
				done
				in !cond
		end
	| Forall([], expr) -> sal_expr_to_lisp ctx expr
	| Exists(_) -> failwith "exists"

	| Not(e) -> Not(sal_expr_to_lisp ctx e)
	| Neq(a, b) -> Not(sal_expr_to_lisp ctx (Eq(a, b)))
  
  | Opp(_) -> failwith "opp"
  | Sub(_) -> failwith "sub"
  | Mul(_) -> failwith "mul"
  | Div(_) -> failwith "div"
  | And(a, b) -> And(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)
  | Or(a, b) -> Or(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)
  | Xor(_) | Implies(_) | Iff(_) 
  | Exists(_) -> failwith "exists"
  | Let(_) -> failwith "logic"


let sal_real_assignment_to_state ctx =
	let to_condition = function
	| Assign(n, expr) ->
		begin
		match expr with
		| Array_literal(name, type_data, expr) -> failwith "Array litteral unsupported"
		| _ -> Equality(sal_expr_to_lisp ctx n, sal_expr_to_lisp ctx expr)
		end
	| Member(n, Set_literal(in_name, t, expr)) ->
		let intermediate_context = StrMap.add in_name (Expr(sal_expr_to_lisp ctx n, sal_type_to_sally_type ctx t)) ctx in
		sal_expr_to_lisp intermediate_context expr
	in
	List.fold_left (fun l a -> Lispy_ast.And(l, to_condition a)) True

let sal_init_to_state ctx type_name name assign =
	name, type_name, sal_real_assignment_to_state ctx assign

let sal_transition_to_transition ctx n = function
| NoTransition -> failwith "notransition"
| GuardedCommands(l) ->
	let all_guarded = List.filter (function | Guarded(_) -> true | _ -> false) l in
	let all_conditions = List.fold_left (fun l a ->
		match a with
		| Guarded(expr, _) ->
			let guard = sal_expr_to_lisp ctx expr in
			Lispy_ast.And(l, Lispy_ast.Not(guard))
		| _ -> raise Not_found
		) True all_guarded
	in

	let cond = List.fold_left (fun l a -> match a with
	| Default(assign) -> Lispy_ast.Or(l, And(all_conditions, sal_real_assignment_to_state ctx assign))
	| Guarded(expr, assignment) ->
		let guard = sal_expr_to_lisp ctx expr in
		let implies = sal_real_assignment_to_state ctx assignment in
		Or(l, And(guard, implies))
	) False l in
	"trans", n, cond

let sal_module_to_lisp ctx (name, sal_module) =
	let type_init_ctx, transition_ctx, state_type = sal_state_vars_to_state_type ctx name sal_module.state_vars in
	let initial_state = sal_init_to_state type_init_ctx name "init" sal_module.initialization in
	let transitions = sal_transition_to_transition transition_ctx name sal_module.transition in
	type_init_ctx, (name, state_type, initial_state, transitions)

let sal_query_to_lisp ctx systems (name, _, model_name, expr) =
	let type_init_ctx, transition_system = List.find (fun (_, (n, _, _, _)) -> n = model_name) systems in
	((transition_system, sal_expr_to_lisp (ctx_union ctx type_init_ctx) expr):query)

let sal_context_to_lisp ctx =
	let name = ctx.ctx_name in
	let defs = ctx.definitions in
	let sally_ctx = StrMap.empty in
	let _, queries, _ =
		List.fold_left (fun (transition_systems, queries, sally_ctx) -> function
		| Module_def(a, b) ->
			let sally_module = sal_module_to_lisp sally_ctx (a,b) in
			sally_module::transition_systems, queries, sally_ctx
		| Assertion(a,b,c,d) ->
			let q = sal_query_to_lisp sally_ctx transition_systems (a,b,c,d) in
			transition_systems, q::queries, sally_ctx
		| Constant_def(name, sal_type, expr) ->
			transition_systems, queries,
			StrMap.add name (Expr(sal_expr_to_lisp sally_ctx expr, sal_type_to_sally_type sally_ctx sal_type)) sally_ctx
		| Constant_decl(name, sal_type) ->
			transition_systems, queries,
			(* TODO: value?? *)
			StrMap.add name (Expr(Value("1"), sal_type_to_sally_type sally_ctx sal_type)) sally_ctx
		| Function_def(name, l, t, expr) ->
			let var_list = List.(concat @@ map (fun (arg_list, arg_type) ->
				let sally_type = sal_type_to_sally_type sally_ctx arg_type in
				map (fun s -> s, sally_type) arg_list) l) in
			transition_systems, queries,
			StrMap.add name (Fun(var_list, expr)) sally_ctx
		| Type_def(name, sal_type) ->
			transition_systems, queries,
			StrMap.add name (Type(sal_type_to_sally_type sally_ctx sal_type)) sally_ctx
		| _ -> transition_systems, queries, sally_ctx
		) ([], [], sally_ctx) defs in
	
	
	(queries:query list)

