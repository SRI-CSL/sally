open Lisp_ast
open Sal_ast

exception Not_implemented

module StrMap = Map.Make(String)

type sally_substitution =
	Expr of sally_condition
	| Fun of string list * sal_expr
	| Type of sally_type

type sally_context = sally_substitution StrMap.t

exception CannotUseFunctionAsExpression
exception CannotUseExpressionAsFunction

let ctx_union a b =
	StrMap.fold (fun k v c -> StrMap.add k v c) a b

let eval_sally ctx = function
	| Value(s) -> s

let eval_sal ctx = function
	| Decimal(i) -> Value (string_of_int i)
	| Float(i) -> Value(string_of_float i)

	| Ident(s) -> (match StrMap.find s ctx with
		| Expr(s) -> Value(eval_sally ctx s)
		| _ -> raise CannotUseFunctionAsExpression)
	| _ -> failwith "couldn't statically evaluate"

exception UnknownType of string

let rec sal_type_to_sally_type ctx = function
	| Base_type("NATURAL") -> Real
	| Base_type(e) -> (match StrMap.find e ctx with
		| Type(t) -> t
		| _ -> raise (UnknownType(e))
		)
	| Array(t1, t2) -> Lisp_ast.Array(sal_type_to_sally_type ctx t1, sal_type_to_sally_type ctx t2)
	| Range(i1, i2) ->
		match eval_sal ctx i1, eval_sal ctx i2 with
		| Value(a), Value(b) -> Lisp_ast.Range (int_of_string a, int_of_string b)
		| _ -> failwith "couldn't evaluate properly"

let sal_state_vars_to_state_type (ctx:sally_context) name vars =
	let sally_vars = List.(concat @@ map (fun (_, declarations) ->
		concat @@ map (fun (ids, ty) ->
		let t = sal_type_to_sally_type ctx ty in
		map (fun n -> n, t) ids) declarations) vars) in

	let type_init_ctx = List.fold_left
		(fun ctx (n, t) ->
			StrMap.add n (Expr (Lisp_ast.Ident(n))) ctx
		) ctx sally_vars in

	let transition_ctx = List.fold_left
		(fun ctx (n, t) ->
			let ctx = StrMap.add n (Expr(Lisp_ast.Ident ("state."^n))) ctx in
			StrMap.add (n^"'") (Expr(Lisp_ast.Ident("next."^n))) ctx
		) ctx sally_vars in

	type_init_ctx, transition_ctx, ((name, sally_vars):state_type)

exception InadequateArrayUse

let rec sal_expr_to_lisp (ctx:sally_context) = function
	| Decimal(i) -> Value (string_of_int i)
	| Float(i) -> Value(string_of_float i)

	| Ident(s) -> (match StrMap.find s ctx with
		| Expr(s) -> s
		| _ -> raise CannotUseFunctionAsExpression)

	| Eq(a, b) -> Equality(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)
	| Ge(a, b) -> GreaterEqual(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)
	| Implies(a, b) -> Or(Not(sal_expr_to_lisp ctx a), sal_expr_to_lisp ctx b)
	| Add(a, b) -> Lisp_ast.Add(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)

	| Next(s) -> (failwith ("Next ? " ^ s))

	| Funcall("G", [l]) -> sal_expr_to_lisp ctx l
	| Funcall(name, args_expr) -> (match  StrMap.find name ctx with
		| Fun(decls, expr) ->
			let args = List.combine decls (List.map (sal_expr_to_lisp ctx) args_expr) in
			let inside_function_ctx = List.fold_left (fun ctx (arg_name, arg_value) ->
				StrMap.add arg_name (Expr(arg_value)) ctx) ctx args in
			sal_expr_to_lisp inside_function_ctx expr
		| _ -> raise CannotUseExpressionAsFunction
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


let sal_real_assignment_to_state ctx =
	let to_condition = function
	| Assign(n, expr) -> Equality(sal_expr_to_lisp ctx n, sal_expr_to_lisp ctx expr)
	in
	List.fold_left (fun l a -> Lisp_ast.And(l, to_condition a)) True

let sal_init_to_state type_init_ctx type_name name assign =
	let to_condition = function
	| Assign(n, expr) -> Equality(sal_expr_to_lisp type_init_ctx n, sal_expr_to_lisp type_init_ctx expr)
	in
	name, type_name, List.fold_left (fun l a -> Lisp_ast.And(l, to_condition a)) True assign

let sal_transition_to_transition ctx n = function
| NoTransition -> failwith "notransition"
| GuardedCommands(l) ->
	let all_guarded = List.filter (function | Guarded(_) -> true | _ -> false) l in
	let all_conditions = List.fold_left (fun l a ->
		match a with
		| Guarded(expr, _) ->
			let guard = sal_expr_to_lisp ctx expr in
			Lisp_ast.And(l, Lisp_ast.Not(guard))
		| _ -> raise Not_found
		) True all_guarded
	in

	let cond = List.fold_left (fun l a -> match a with
	| Default(assign) -> Lisp_ast.Or(l, And(all_conditions, sal_real_assignment_to_state ctx assign))
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
			StrMap.add name (Expr(sal_expr_to_lisp sally_ctx expr)) sally_ctx
		| Function_def(name, l, t, expr) ->
			let var_list = List.(concat @@ map fst l) in
			transition_systems, queries,
			StrMap.add name (Fun(var_list, expr)) sally_ctx
		| Type_def(name, sal_type) ->
			transition_systems, queries,
			StrMap.add name (Type(sal_type_to_sally_type sally_ctx sal_type)) sally_ctx
		| _ -> transition_systems, queries, sally_ctx
		) ([], [], sally_ctx) defs in
	
	
	(queries:query list)

