open Lisp_ast
open Sal_ast

exception Not_implemented

let sal_type_to_sally_type _ = Real

let sal_state_vars_to_state_type name vars =
	name, List.(concat @@ map (fun (_, declarations) ->
		concat @@ map (fun (ids, ty) ->
		let t = sal_type_to_sally_type ty in
		map (fun n -> n, t) ids) declarations) vars)

let rec sal_expr_to_lisp ?nonext:(nonext=false) = function
| Decimal(i) -> Value (string_of_int i)
| Float(i) -> Value(string_of_float i)
| Ident(s) -> if s.[String.length s - 1] = '\'' then
	Ident("next." ^ (String.sub s 0 (String.length s - 1)))
	else if not nonext then
	Ident("state." ^ s)
	else
	Ident(s)
| Eq(a, b) -> Equality(sal_expr_to_lisp ~nonext:nonext a, sal_expr_to_lisp ~nonext:nonext b)
| Ge(a, b) -> GreaterEqual(sal_expr_to_lisp ~nonext:nonext a, sal_expr_to_lisp ~nonext:nonext b)
| Implies(a, b) -> Or(Not(sal_expr_to_lisp ~nonext:nonext a), sal_expr_to_lisp ~nonext:nonext b)

let sal_real_assignment_to_state =
	let to_condition = function
	| Assign(SVar(n), expr) -> Equality(Ident("state."^n), sal_expr_to_lisp expr)
	| Assign(NVar(n), expr) -> Equality(Ident("next."^n), sal_expr_to_lisp expr)
	in
	List.fold_left (fun l a -> Lisp_ast.And(l, to_condition a)) True

let sal_init_to_state type_name name assign =
	let to_condition = function
	| Assign(SVar(n), expr) -> Equality(Ident(n), sal_expr_to_lisp ~nonext:true expr)
	in
	name, type_name, List.fold_left (fun l a -> Lisp_ast.And(l, to_condition a)) True assign

let sal_transition_to_transition n = function
| NoTransition -> failwith "notransition"
| GuardedCommands(l) -> let cond = List.fold_left (fun l a -> match a with
	| Default(l) -> sal_real_assignment_to_state l
	| Guarded(expr, assignment) -> Or(l, And(sal_expr_to_lisp expr, sal_real_assignment_to_state assignment))
	) False l in
	"trans", n, cond

let sal_module_to_lisp defs (name, sal_module) =
	let state_type = sal_state_vars_to_state_type name sal_module.state_vars in
	let initial_state = sal_init_to_state name "init" sal_module.initialization in
	let transitions = sal_transition_to_transition name sal_module.transition in
	name, state_type, initial_state, transitions

let sal_query_to_lisp defs systems (name, _, model_name, expr) =
	let a = List.find (fun (n, _, _, _) -> n = model_name) systems in
	((a, sal_expr_to_lisp ~nonext:true expr):query)

let sal_context_to_lisp ctx =
	let name = ctx.ctx_name in
	let defs = ctx.definitions in
	let modules_def = List.filter (function | Module_def(_) -> true | _ -> false) defs in
	let modules_def = List.map (function | Module_def(a, b) -> a,b | _ -> raise Not_found) modules_def in
	
	let assertion_defs = List.filter (function | Assertion(_) -> true | _ -> false) defs in
	let assertion_defs = List.map (function | Assertion(a, b, c, d) -> a,b,c,d | _ -> raise Not_found)
		assertion_defs in
	
	let transition_systems = List.map (sal_module_to_lisp defs) modules_def in
	
	let queries = List.map (sal_query_to_lisp defs transition_systems) assertion_defs in
	(queries:query list)

