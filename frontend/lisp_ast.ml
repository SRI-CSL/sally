(* Abstract syntax for the lispy style of the .mcmt files read by Sally *)

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

type indentation = In | Out | None
let print_to_ft f ?nl:(nl=false) ?i:(i=None) s =
	(match i with
	| In -> f.i <- f.i + 1
	| Out -> f.i <- f.i - 1
	| None -> ());
	if i = In || nl then
		Format.fprintf f.ft "%s\n%s" s (String.make (f.i) '\t')
	else if i = Out && f.i = 0 then
		Format.fprintf f.ft "%s@." s
	else
		Format.fprintf f.ft "%s" s;

type fmt = ?nl:bool -> ?i:indentation->string->unit

let rec get_expr_depth = function
	| Value(_) | True | False | Ident(_) -> 1
	| Equality(a, b) | GreaterEqual(a,b) | Or(a, b) | And(a, b) | Add(a,b) -> (max (get_expr_depth a) (get_expr_depth b)) + 1
	| Not(a) -> 1 + get_expr_depth a

let rec print_expr (f:fmt) =
	let print_folded s a b =
		if get_expr_depth (Equality(a, b)) >= 5 then
			begin
			f ~i:In ("(" ^ s ^ " ");
			print_expr f a; f ~nl:true ""; print_expr f b;
			f ~i:Out ")";
			end
		else
			begin
			f ("(" ^ s ^ " ");
			print_expr f a; f " "; print_expr f b;
			f ")";
			end
	in
	function
	| Equality(a, b) -> print_folded "=" a b
	| Value(s) -> f s
	| Ident(s) -> f s
	| GreaterEqual(a, b) ->
		print_folded ">=" a b
	| Or(a, b) ->
		print_folded "or" a b
	| Add(a, b) ->
		print_folded "+" a b
	| And(a, b) ->
		print_folded "and" a b
	| Not(a) ->
		begin
		f "(not ";
		print_expr f a;
		f ")";
		end
	| True -> f "true"
	| False -> f "false"

let print_transition (f:fmt) ((ident, state_type, sally_cond):transition) =
	f ~i:In ("(define-transition " ^ ident ^ " state");
	f ~nl:true "";
	print_expr f sally_cond;
	f ~i:Out ")"

let print_state (f:fmt) ((ident, state_type, sally_cond):state) =
	f ~i:In ("(define-states " ^ ident ^ " state");
	f ~nl:true "";
	print_expr f sally_cond;
	f ~i:Out ")"


let sally_type_to_string = function
| Real -> "Real"
| Bool -> "Bool"
| Range(_, _) -> "Real"
| Array(_, _) -> "Real"

let print_state_type (f:fmt) (ident, var_list) =
	f ~i:In ("(define-state-type state");
	f ~nl:true "(";
	let rec print_variable (name, sally_type) =
		match sally_type with
		| Array(Range(array_inf, array_sup), b) ->
			begin
			for i = array_inf to array_sup do
				print_variable (name ^ "!" ^ string_of_int i, b);
			done;
			end
		| _ ->
			f ~nl:true ("(" ^ name ^ " " ^ (sally_type_to_string sally_type) ^ ")")
	in
	List.iter print_variable var_list;
	f ~i:Out "))"

let print_ts (f:fmt) (name, state_type, init, transition) =
	print_state_type f state_type;
	print_state f init;
	print_transition f transition;
	f ~i:In ("(define-transition-system " ^ name);
	f ~nl:true "state";
	f ~nl:true "init";
	f "trans";
	f ~i:Out ")"

let print_query ch q =
	let ft = {ft= Format.formatter_of_out_channel ch; i=0} in
	let f = print_to_ft ft in
	let transition_system, cond = q in
	print_ts f transition_system;
	f ~i:In ("(query " ^ (ts_name transition_system));
	print_expr f cond;
	f ~i:Out ") "
