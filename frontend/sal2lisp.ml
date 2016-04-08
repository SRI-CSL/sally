open Lisp_ast
open Sal_ast

exception Not_implemented

module StrMap = Map.Make(String)

type sally_substitution =
	Expr of sally_condition
	| Fun of string list * sal_expr

type sally_context = sally_substitution StrMap.t

let ctx_union a b =
	StrMap.fold (fun k v c -> StrMap.add k v c) a b

let sal_type_to_sally_type _ = Real

let sal_state_vars_to_state_type (ctx:sally_context) name vars =
	let sally_vars = List.(concat @@ map (fun (_, declarations) ->
		concat @@ map (fun (ids, ty) ->
		let t = sal_type_to_sally_type ty in
		map (fun n -> n, t) ids) declarations) vars) in
	let type_init_ctx = List.fold_left (fun ctx (n, t) -> StrMap.add n (Expr (Lisp_ast.Ident(n))) ctx) ctx sally_vars in
	let transition_ctx = List.fold_left (
		fun ctx (n, t) ->
			let ctx = StrMap.add n (Expr(Lisp_ast.Ident ("state."^n))) ctx in
			StrMap.add (n^"'") (Expr(Lisp_ast.Ident("next."^n))) ctx)
		ctx sally_vars in
	type_init_ctx, transition_ctx, (name, sally_vars)

exception CannotUseFunctionAsExpression
exception CannotUseExpressionAsFunction

let rec sal_expr_to_lisp (ctx:sally_context) = function
| Decimal(i) -> Value (string_of_int i)
| Float(i) -> Value(string_of_float i)
| Ident(s) -> (match StrMap.find s ctx with
	| Expr(s) -> s
	| Fun(_) -> raise CannotUseFunctionAsExpression)
| Eq(a, b) -> Equality(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)
| Ge(a, b) -> GreaterEqual(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)
| Implies(a, b) -> Or(Not(sal_expr_to_lisp ctx a), sal_expr_to_lisp ctx b)
| Next(s) -> (failwith ("Next ? " ^ s))
| Funcall("G", [l]) -> sal_expr_to_lisp ctx l
| Funcall(name, args_expr) -> (match  StrMap.find name ctx with
	| Expr(_) -> raise CannotUseExpressionAsFunction
	| Fun(decls, expr) ->
		let args = List.combine decls (List.map (sal_expr_to_lisp ctx) args_expr) in
		let inside_function_ctx = List.fold_left (fun ctx (arg_name, arg_value) ->
			StrMap.add arg_name (Expr(arg_value)) ctx) ctx args in
		sal_expr_to_lisp inside_function_ctx expr
	)
| Add(a, b) -> Lisp_ast.Add(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)
| Cond([], else_term) -> sal_expr_to_lisp ctx else_term
| Cond((a,b)::q, else_term) -> Ite(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b, sal_expr_to_lisp ctx (Cond(q, else_term)))

let sal_real_assignment_to_state ctx =
	let to_condition = function
	| Assign(SVar(n), expr) -> Equality(Ident("state."^n), sal_expr_to_lisp ctx expr)
	| Assign(NVar(n), expr) -> Equality(Ident("next."^n), sal_expr_to_lisp ctx expr)
	in
	List.fold_left (fun l a -> Lisp_ast.And(l, to_condition a)) True

let sal_init_to_state type_init_ctx type_name name assign =
	let to_condition = function
	| Assign(SVar(n), expr) ->
		Equality(Ident(n), sal_expr_to_lisp type_init_ctx expr)
	in
	name, type_name, List.fold_left (fun l a -> Lisp_ast.And(l, to_condition a)) True assign

let sal_transition_to_transition ctx n = function
| NoTransition -> failwith "notransition"
| GuardedCommands(l) -> let cond = List.fold_left (fun l a -> match a with
	| Default(assign) -> Lisp_ast.Or(l, sal_real_assignment_to_state ctx assign)
	| Guarded(expr, assignment) -> Or(l, And(sal_expr_to_lisp ctx expr, sal_real_assignment_to_state ctx assignment))
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
		| _ -> transition_systems, queries, sally_ctx
		) ([], [], sally_ctx) defs in
	
	
	(queries:query list)

