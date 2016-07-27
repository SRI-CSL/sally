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

module StrMap = Map.Make(String)

type sally_substitution =
  | Expr     of sally_condition * sally_type
  | Fun      of (string * sally_type) list * sal_expr
  | Type     of sally_type
  | Array of sal_expr * sally_context * sally_type
and
sally_context = sally_substitution StrMap.t

exception Not_implemented
exception Cannot_use_function_as_expression
exception Cannot_use_expression_as_function of string
exception Inadequate_array_use
exception Inadequate_array_index
exception Member_without_set
exception Iteration_on_non_range_type
exception Need_transition
exception Unknown_type of string
exception Bad_left_hand_side
exception Unsupported_array_type
exception Variable_not_found of string


(** Union of two contexts, if a key is present in both a and b, the association in a in on top of
  * the one in b *)
let ctx_union a b =
  StrMap.fold (fun k v c -> StrMap.add k v c) a b

(** Add a substitution in the context *)
let ctx_add_substition ctx a b =
  StrMap.add a b ctx

(** Tries to statically evaluate a sally expression.
  * This is used to handle parametrized systems: as of now, sally can not handle generalized array,
  * i.e. if a type [1..N] is defined, N must be known, thus it has to be evaluated before generating
  * the corresponding lispy for low level sally.
  **)
let eval_sally ctx = function
  | Value(s) -> s
  | _ -> raise Not_implemented

let rec seq i = function
  | x when x = i -> [i]
  | n -> n::(seq i (n-1))

let ctx_add_expr name v ty ctx =
  StrMap.add name (Expr(v, ty)) ctx

let ctx_var name ctx =
  try
    StrMap.find name ctx
  with
  | Not_found -> raise (Variable_not_found name)

let next_var name ctx =
  try
    StrMap.find (name ^ "'") ctx
  with
  | Not_found ->
    ctx_var name ctx

let prev_var name ctx =
  let l = String.length name - 1 in
  if name.[l] = '\'' then
    let sname = String.sub name 0 l in
    ctx_var sname ctx
  else ctx_var name ctx
               
(** Convert a sal type to a lispy one, based on the information contained in ctx *)
let rec sal_type_to_sally_type ctx ?name:(name="anonymous") = function
  | Base_type("NATURAL" as e) | Base_type ("INTEGER" as e) ->
    (* FIXME: need a real natural type *)
    Format.eprintf "Warning: %s converted to real automatically.@." e;
    Real
  | Base_type("BOOLEAN") -> Bool
  | Base_type("REAL") -> Real
  | Base_type(e) -> (
      try match StrMap.find e ctx with
        | Type(t) -> t
        | _ -> raise (Unknown_type(e))
      with | Not_found -> raise (Unknown_type e)
    )
  | Array(t1, t2) ->
    let t1 = sal_type_to_sally_type ctx t1 in
    let t2 = sal_type_to_sally_type ctx t2 in
    Lispy_ast.Array(t1, t2)
  | Enum(l) -> Real
  | Subtype(_) -> Real
  | Process -> IntegerRange name
  | Range(i1, i2) -> (* FIXME: need to check it stays natural and inside the range *)
    let sally_expr_from = sal_expr_to_lisp ctx i1
    and sally_expr_to = sal_expr_to_lisp ctx i2 in

    let from_as_string = eval_sally ctx sally_expr_from
    and to_as_string = eval_sally ctx sally_expr_to in
    Lispy_ast.Range (int_of_string from_as_string, int_of_string to_as_string)
and
  get_disjonctions_from_array ctx = function
  | Array_access(Ident(s), a) ->
    begin
      let open Lispy_ast in
      let index_expr = sal_expr_to_lisp ctx a in
      match StrMap.find s ctx with
      | Expr(Ident(n, _), Array(Range(array_start, array_end), dest_type)) ->
        begin
          match index_expr with
          | Value(s) ->
            let s' = int_of_string s in
            assert(array_start <= s' && s' <= array_end);
            [True, Ident(n ^ "!" ^ s, dest_type)]
          | a ->
            let l = seq array_start array_end in
            List.map (fun i ->
                (Equality(index_expr, Value(string_of_int i)), Lispy_ast.Ident(n ^ "!" ^ string_of_int i, dest_type))) l
        end
      | Expr(a, Array(IntegerRange(_), dest_type)) ->
        [True, Lispy_ast.Select(a, index_expr)]
      | Expr(Ident(n, _), t) ->
        Io.Sal_writer.print_expr stdout a;
        Format.printf "%s %s@." n (Io.Lispy_writer.sally_type_to_debug t);
        raise Inadequate_array_index
      | Array(Array_literal(name, data_type, expr), old_ctx, _) ->
        let old_ctx = ctx_add_substition old_ctx name (Expr(index_expr, sal_type_to_sally_type ctx data_type)) in
        [True, sal_expr_to_lisp old_ctx expr]
      | Array(sal_expr, old_ctx, data_type) ->
        let tmp_ctx = ctx_add_substition ctx s (Expr (sal_expr_to_lisp old_ctx sal_expr, data_type)) in
        get_disjonctions_from_array tmp_ctx (Array_access(Ident(s), a))
      | _ -> raise Inadequate_array_use
    end
  | Array_access(Array_access(a, b), index) ->
    let sub_array = Array_access(a,b) in
    let all_sub_disjs = get_disjonctions_from_array ctx sub_array in
    List.(concat @@ map (fun (disj, sub_array_cell) ->
        let sub_array_cell_name, dest_type =
          match sub_array_cell with
          | Lispy_ast.Ident(sub, dest_type) -> sub, dest_type
          | _ -> failwith "should be ident"
        in
        let tmp_ctx = StrMap.add sub_array_cell_name (Expr(sub_array_cell, dest_type)) ctx in
        map (fun (sub_disj, array_cell) ->
            (Lispy_ast.And(disj, sub_disj), array_cell)
          ) @@ get_disjonctions_from_array tmp_ctx (Array_access(Ident(sub_array_cell_name), index))) all_sub_disjs)
  | _ -> raise Inadequate_array_use
and
  (** Convert a sal expr to a lispy condition, based on the information contained in ctx *)
  sal_expr_to_lisp (ctx:sally_context) = function
  | Decimal(i) -> Value (string_of_int i)
  | Float(i) -> Value(string_of_float i)
  | Ident(s) -> (match ctx_var s ctx with
      | Expr(s, _) -> s
      | Array(e, old_ctx, _) -> sal_expr_to_lisp old_ctx e
      | _ -> raise Cannot_use_function_as_expression)
  | SProc_cardinal s -> LProc_cardinal s
  | Eq(a, b) -> Equality(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)
  | Ge(a, b) -> GreaterEqual(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)
  | Gt(a, b) -> Greater(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)
  | Lt(a, b) -> Greater(sal_expr_to_lisp ctx b, sal_expr_to_lisp ctx a)
  | Le(a, b) -> GreaterEqual(sal_expr_to_lisp ctx b, sal_expr_to_lisp ctx a)
  | Implies(a, b) -> Or(Not(sal_expr_to_lisp ctx a), sal_expr_to_lisp ctx b)
  | Add(a, b) -> Lispy_ast.Add(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)

  | Next(s) -> (failwith ("Next ? " ^ s))

  | Funcall("G", [l]) -> sal_expr_to_lisp ctx l
  | Funcall(name, args_expr) ->
    begin
      match  StrMap.find name ctx with
      | Fun(decls, expr) ->
        let args = List.combine decls args_expr in
        let inside_function_ctx = List.fold_left (fun nctx ((arg_name, arg_type), arg_value) ->
            match arg_type with
            | Real | Bool -> StrMap.add arg_name (Expr(sal_expr_to_lisp ctx arg_value, arg_type)) nctx
            | Array(_, dest_type) -> StrMap.add arg_name (Array(arg_value, ctx, arg_type)) nctx
          ) ctx args in
        sal_expr_to_lisp inside_function_ctx expr
      | _ -> raise (Cannot_use_expression_as_function name)
    end
  | Cond([], else_term) -> sal_expr_to_lisp ctx else_term
  | Cond((a,b)::q, else_term) ->
    let a = sal_expr_to_lisp ctx a in
    let b = sal_expr_to_lisp ctx b in
    let next_condition = Cond(q, else_term) in
    Ite(a, b, sal_expr_to_lisp ctx next_condition)

  | Array_access(a, b) ->
    let conds = get_disjonctions_from_array ctx (Array_access (a, b)) in
    begin
      match conds with
      | [] -> raise Inadequate_array_use
      | (last_dsj, last_result)::q ->
        (* it's safe to ignore the last conditions, as the index has to be in the array range
           * If it is not the case, then one value is "randomly" (the implementation of
           * get_disjonctions_from_array suggests it is the last array cell) chosen *)
        List.fold_left (fun l (dsj, result) -> Ite(dsj, result, l)) last_result q
    end
  | Set_literal(_) -> failwith "set" 
  | SSet_cardinal(in_name, t, expr) ->
    let st = sal_type_to_sally_type ctx t in
    let intermediate_context = StrMap.add in_name (Expr(Ident (in_name, st), st)) ctx in
    LSet_cardinal (in_name, st, sal_expr_to_lisp intermediate_context expr)
  | Array_literal(n, e, e2) ->
    failwith "Unsupported Array_literal"
  | Forall(t::q, expr) ->
    begin
      match t with
      | [], sal_type -> sal_expr_to_lisp ctx (Forall(q, expr))
      | t::end_decl, sal_type ->
        let sally_type = sal_type_to_sally_type ctx sal_type in
        match sally_type with
        | Range(a, b) ->
          begin
            let cond = ref Lispy_ast.True in
            for i = a to b do
              let (tmp_ctx:sally_context) = StrMap.add t (Expr(Value(string_of_int i), Real)) ctx in
              cond := Lispy_ast.And(!cond, sal_expr_to_lisp tmp_ctx (Forall((end_decl, sal_type)::q, expr)))
            done;
            !cond
          end
        | IntegerRange(n) ->
          let tmp_ctx = ctx_add_expr t (Ident(t, sally_type)) sally_type ctx in
          Lispy_ast.Forall(t, sally_type, sal_expr_to_lisp tmp_ctx (Forall((end_decl, sal_type)::q, expr)))
        | _ -> raise Iteration_on_non_range_type
    end
  | Forall([], expr) -> sal_expr_to_lisp ctx expr
  | Exists(_) -> failwith "exists"

  | Not(e) -> Not(sal_expr_to_lisp ctx e)
  | Neq(a, b) -> Not(sal_expr_to_lisp ctx (Eq(a, b)))
  | True -> Lispy_ast.True
  | False -> Lispy_ast.False

  | Opp(_) -> failwith "opp"
  | Sub(a,b) -> Sub(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)
  | Mul(a, b) -> Mul(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)
  | Div(a,b) -> Div(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)
  | And(a, b) -> And(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)
  | Or(a, b) -> Or(sal_expr_to_lisp ctx a, sal_expr_to_lisp ctx b)
  | Xor(_) | Iff(_) -> failwith "xor implies iff"
  | Let(_) -> failwith "logic"


let sal_state_vars_to_state_type (ctx:sally_context) name vars =
  let sally_vars = List.(concat @@ map (fun (_, declarations) ->
      concat @@ map (fun (ids, ty) ->
          let t = sal_type_to_sally_type ctx ty in
          map (fun n -> n, t) ids) declarations) vars) in

  let type_init_ctx = List.fold_left
      (fun ctx (n, t) ->
         StrMap.add n (Expr (Lispy_ast.Ident(n, t), t)) ctx
      ) ctx sally_vars in

  let transition_ctx = List.fold_left
      (fun ctx (n, t) ->
         let ctx = StrMap.add n (Expr(Lispy_ast.Ident ("state."^n, t), t)) ctx in
         StrMap.add (n^"'") (Expr(Lispy_ast.Ident("next."^n, t), t)) ctx
      ) ctx sally_vars in

  type_init_ctx, transition_ctx, ((name, sally_vars):state_type)

let rec infer_type ctx = function
  | Array_literal(_, a, expr) -> Ast.Lispy_ast.Array(sal_type_to_sally_type ctx a, infer_type ctx expr)
  | _ -> Real

(** Converts a list of sal_assignments to a single big lispy condition *) 
let sal_assignments_to_condition ?only_define_type:(only_type=false) ?vars_to_define:(s=[]) ctx assignment =
  let variables_to_init = ref s in
  let forget_variable n =
    variables_to_init := List.filter (fun (name, _) -> (name ^ "'") <> n) !variables_to_init
  in
  let rec to_condition ctx = function
    | Assign ((Ident lhs_name) as n, expr) ->
      begin
        forget_variable lhs_name;
        (* check equality_type *)
        match expr with
        | Array_literal(name, type_data, expr) ->
          begin
            match sal_type_to_sally_type ctx type_data with
            | Range(a, b) ->
              List.fold_left (fun l i ->
                  let si = string_of_int i in
                  let type_infered = infer_type ctx expr in
                  let variable_value = Value(si) in
                  let cell_value = lhs_name ^ "!" ^ si in
                  let tmp_ctx = ctx_add_substition ctx name (Expr(variable_value, Real)) in
                  let tmp_ctx = ctx_add_substition tmp_ctx cell_value (Expr(Ident(cell_value, type_infered), type_infered)) in
                  let constraint_i = to_condition tmp_ctx (Assign(Ident(lhs_name ^ "!" ^ (si)), expr)) in
                  Lispy_ast.And(l, constraint_i)
                ) Lispy_ast.True (seq a b)
            | _ -> failwith "unsupported index type for array literal"
          end
        | _ ->
          match ctx_var lhs_name ctx with
          | Expr(Ident(sally_lhs, _), Array(Range(a, b), t)) ->
            List.map (fun i ->
                let cell_name = sally_lhs ^ "!" ^ string_of_int i in
                let ctx = ctx_add_substition ctx cell_name (Expr(Ident(cell_name, t), t)) in
                to_condition ctx (Assign(Ident cell_name, Array_access(expr, Decimal i)))
              ) (seq a b)
            |> List.fold_left Lispy_ast.and_ Lispy_ast.True
          | Expr(_, Array(_, _)) ->
            failwith "equality not supported for every arrays"
          | _ -> Equality(sal_expr_to_lisp ctx n, sal_expr_to_lisp ctx expr)
      end
    | Assign(Array_access(Ident id, index), expr) ->
      forget_variable id;
      begin
        match ctx_var id ctx, prev_var id ctx with
        | Expr(i, Array _), Expr(pi, Array _) ->
          let lexpr = sal_expr_to_lisp ctx expr in
          let lindex  = sal_expr_to_lisp ctx index in
          Lispy_ast.Equality(i, Lispy_ast.Store (pi, lindex, lexpr))
        | _ -> assert false
      end
    | Member(n, Set_literal(in_name, t, expr)) ->
      let () = 
        match n with
          | Ident(name) -> forget_variable name
          | _ -> raise Bad_left_hand_side
      in
      let intermediate_context = StrMap.add in_name (Expr(sal_expr_to_lisp ctx n, sal_type_to_sally_type ctx t)) ctx in
      sal_expr_to_lisp intermediate_context expr
    | Member(_) -> raise Member_without_set
  in
  let explicit_condition = List.fold_left (
      fun l a ->
        Lispy_ast.And(l, to_condition ctx a)
    ) True assignment in
  let rec get_equality_term equality_function ctx = function
    | (name, Lispy_ast.Array(Range(a,b), t)) ->
      let cond = ref Lispy_ast.True in
      let lispy_ident, lispy_next_ident = StrMap.find name ctx, next_var name ctx
      in
      (match lispy_ident, lispy_next_ident with
       | Expr(Ident(lispy_ident,_), _), Expr(Ident(lispy_next_ident, _), _) ->
         begin
           for i = a to b do
             let ident = name ^ "!" ^ string_of_int i in
             let lispy_ident_i = lispy_ident ^ "!" ^ string_of_int i in
             let lispy_next_ident_i = lispy_next_ident ^ "!" ^ string_of_int i in
             let (tmp_ctx:sally_context) = StrMap.add ident (Expr(Ident(lispy_ident_i, t), t)) ctx in
             let (tmp_ctx:sally_context) = StrMap.add (ident ^ "'") (Expr(Ident(lispy_next_ident_i, t), t)) tmp_ctx in
             cond := Lispy_ast.And(!cond, get_equality_term equality_function tmp_ctx (ident, t));
           done;
           !cond
         end
       | _ -> raise Not_found)
    | (name, Array(IntegerRange(s), t)) -> equality_function ctx (name, Lispy_ast.Array(IntegerRange(s), t))
    | (name, Array(_, t)) -> raise Unsupported_array_type
    | (name, ty) -> equality_function ctx (name, ty)
  in
  let real_equality_function ctx (name, ty) = Equality(sal_expr_to_lisp ctx (Ident name), sal_expr_to_lisp ctx (Ident (name ^ "'"))) in
  let fake_equality_function ctx (name, ty) = match ty with
    | Lispy_ast.Range(a, b) ->
      begin
        let expr = match next_var name ctx with
          | Expr(a, _) -> a
          | _ -> raise Cannot_use_function_as_expression
        in
        List.fold_left (fun l i ->
            Lispy_ast.Or(l, Equality(expr, Value (string_of_int i)))
          ) False (seq a b)
      end
    | _ -> True
  in
  let type_condition =
    List.fold_left (
      fun l var ->
        Lispy_ast.And(l, get_equality_term fake_equality_function ctx var)
    ) True s
  in
  let implicit_condition =
    if only_type then
      Lispy_ast.True
    else
      List.fold_left (
        fun l var ->
          Lispy_ast.And(l, get_equality_term real_equality_function ctx var)
      ) True !variables_to_init in
  Lispy_ast.(And(type_condition, And(explicit_condition, implicit_condition)))

(** Converts an assignment to a lispy state of type {i type_name} and named {i name} *)
let sal_assignments_to_lispy_state ctx state_type name assign =
  let type_name, vars_to_define = state_type in
  {	id = name;
    state_type_id = type_name;
    condition = sal_assignments_to_condition ~only_define_type:true ~vars_to_define ctx assign; }

(** Takes a Sal transition and return a lispy one.
  * @param ctx a sally_context
  * @param transition_name the trasition systen name, usually the sal module name
*)
let sal_transition_to_transition ((type_name, variables):state_type) ctx transition_name = function
  | NoTransition -> raise Need_transition
  | Assignments(assign) (* Unguarded transitions *) -> 
    {	id = "trans";
      state_type_id = transition_name;
      formula = sal_assignments_to_condition ~vars_to_define:variables ctx assign; }
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

    let rec compute_condition ctx l = function
      | Default(assign) ->
        Lispy_ast.Or(l,
                     And(all_conditions, sal_assignments_to_condition ~vars_to_define:variables ctx assign)
                    )
      | ExistentialGuarded(existential_vars, guard) ->
        begin
          match existential_vars with
          | [], sal_type -> compute_condition ctx l guard
          | t::end_decl, sal_type ->
            let sally_type = sal_type_to_sally_type ctx sal_type in
            match sally_type with
            | Range(a, b) ->
              List.fold_left (fun l i ->
                  let tmp_ctx = ctx_add_expr t (Value (string_of_int i)) Real ctx in
                  compute_condition tmp_ctx l (ExistentialGuarded((end_decl, sal_type), guard))
                ) l (seq a b)
            | IntegerRange(s) ->
              let tmp_ctx = ctx_add_expr t (Ident (t, IntegerRange(s))) Real ctx in
              Lispy_ast.Or(l, Lispy_ast.Exists(t, IntegerRange(s), compute_condition tmp_ctx False (ExistentialGuarded((end_decl, sal_type), guard))))

            | _ -> raise Iteration_on_non_range_type
        end
      | Guarded(expr, assignment) ->
        let guard = sal_expr_to_lisp ctx expr in
        let implies = sal_assignments_to_condition ~vars_to_define:variables ctx assignment in
        Or(l, And(guard, implies))
    in
    let cond = List.fold_left (compute_condition ctx) False l in
    { id = "trans";
      state_type_id = transition_name;
      formula = cond; }

let add_variable_to_state_type ((name, vars):state_type) var_name var_type =
  ((name, (var_name, var_type)::vars):state_type)

let sal_module_to_lisp undefined_constants ctx (name, sal_module) =
  let ctx = List.fold_left (fun l (n, _) ->
      StrMap.remove n l) ctx undefined_constants in
  let type_init_ctx, transition_ctx, state_type = sal_state_vars_to_state_type ctx name sal_module.state_vars in
  let transition_ctx,type_init_ctx = List.fold_left (fun (l, tyctx) (n,t) ->
      let ctx = StrMap.add n (Expr(Ident("state."^n, t), t)) l in
      let ctx = StrMap.add (n^"'") (Expr(Ident("next."^n, t), t)) ctx in
      let tyctx = StrMap.add n (Expr(Ident(n, t), t)) tyctx in
      ctx, tyctx
    ) (transition_ctx, type_init_ctx) undefined_constants in
  let state_type = List.fold_left (fun st (n,t) ->
      add_variable_to_state_type st n t) state_type undefined_constants in
  let initial_state = sal_assignments_to_lispy_state type_init_ctx state_type "init" sal_module.initialization in
  let transitions = sal_transition_to_transition state_type transition_ctx name sal_module.transition in
  type_init_ctx,
  { id = name;
    state_type = state_type;
    initial_state = initial_state;
    transition = transitions; }

(** Takes a sal assertion and returns a lispy query. The model used in the assertion must already
  * exist in the systems list of transition system.
  * As of now, the second assertion argument, the argument_tag (which is either Lemma or Theorem) is
  * ignored.
*)
let sal_query_to_lisp ctx systems (name, _, model_name, expr) =
  let type_init_ctx, transition_system = List.find (fun (_, ts) -> ts.id = model_name) systems in
  { transition_system = transition_system;
    condition = sal_expr_to_lisp (ctx_union ctx type_init_ctx) expr; }

let sal_context_to_lisp ctx =
  let defs = ctx.definitions in
  let sally_ctx = StrMap.empty in
  let undefined_constants = ref [] in
  let _, queries, sally_env =
    List.fold_left (fun (transition_systems, queries, sally_ctx) -> function
        | Module_def(a, b) ->
          let sally_module = sal_module_to_lisp !undefined_constants sally_ctx (a,b) in
          sally_module::transition_systems, queries, sally_ctx
        | Assertion(a,b,c,d) ->
          let q = sal_query_to_lisp sally_ctx transition_systems (a,b,c,d) in
          transition_systems, queries @ [q], sally_ctx
        | Constant_def(name, sal_type, expr) ->
          transition_systems, queries,
          StrMap.add name (Expr(sal_expr_to_lisp sally_ctx expr, sal_type_to_sally_type sally_ctx sal_type)) sally_ctx
        | Constant_decl(name, sal_type) ->
          begin
            let sally_type = sal_type_to_sally_type sally_ctx sal_type in
            undefined_constants := (name, sally_type)::!undefined_constants;
            transition_systems, queries,
            (* TODO: value?? *)

            StrMap.add name (Expr(Ident(name, sally_type), sally_type)) sally_ctx
          end
        | Function_def(name, l, t, expr) ->
          let var_list = List.(concat @@ map (fun (arg_list, arg_type) ->
              let sally_type = sal_type_to_sally_type sally_ctx arg_type in
              map (fun s -> s, sally_type) arg_list) l) in
          transition_systems, queries,
          StrMap.add name (Fun(var_list, expr)) sally_ctx
        | Type_def(name, sal_type) ->
          transition_systems, queries,
          StrMap.add name (Type(sal_type_to_sally_type ~name sally_ctx sal_type)) sally_ctx
        | Type_decl(n) -> raise Not_implemented
      ) ([], [], sally_ctx) defs in

  let extract_integer_ranges s =
    StrMap.fold (fun k v param_types ->
        match v with
        | Type(IntegerRange(s)) -> s::param_types
        | _ -> param_types
      ) s []
  in


  { queries = (queries:query list);
    parametrized_types = extract_integer_ranges sally_env; }

(* Local Variables: *)
(* compile-command: "make -C ../../build/ -j 4" *)
(* caml-annot-dir: "../../build/frontend/converter/" *)
(* End: *)
