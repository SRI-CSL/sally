open Ast.Sal_ast;;
open Inline;;
open Utils;;
open Format;;

exception Unimplemented of string;;
exception Expected_guarded_command of string;;
exception Duplicate_else_guarded_commands;;

(* call inline function and remove conditional expressions *)
let rec expr_ast_to_str = function
  | Ge (e1, e2) -> "ge("^(expr_ast_to_str e1)^" , "^(expr_ast_to_str e2)^")"
  | Gt (e1, e2) -> "gt("^(expr_ast_to_str e1)^" , "^(expr_ast_to_str e2)^")"
  | Le (e1, e2) -> "le("^(expr_ast_to_str e1)^" , "^(expr_ast_to_str e2)^")"
  | Lt (e1, e2) -> "lt("^(expr_ast_to_str e1)^" , "^(expr_ast_to_str e2)^")"
  | Eq (e1, e2) -> "eq("^(expr_ast_to_str e1)^" , "^(expr_ast_to_str e2)^")"
  | Neq (e1, e2) -> "neq("^(expr_ast_to_str e1)^" , "^(expr_ast_to_str e2)^")"
  | And(e1, e2) -> "and("^(expr_ast_to_str e1)^", "^(expr_ast_to_str e2)^")"
  | Or(e1, e2) -> "or("^(expr_ast_to_str e1)^", "^(expr_ast_to_str e2)^")"
  | Not e -> "not("^(expr_ast_to_str e)^")"
  | True -> "true"
  | False -> "false"
  | Decimal i -> string_of_int i
  | Float f -> string_of_float f
  | Ident str -> str 
  | Cond (ifs, els) -> (List.fold_left (^) "cond(" (List.map (fun x -> (expr_ast_to_str (fst x))^" ; ") ifs))^(expr_ast_to_str els)^")"
  | Add (e1, e2) -> "("^(expr_ast_to_str e1)^"+"^(expr_ast_to_str e2)^")"
  | _ -> "expr";;

let assigns_to_str = function
  | Assign (e1, e2) -> (expr_ast_to_str e1)^":="^(expr_ast_to_str e2)^"\n  "
  | _ -> "member"

let guard_ast_to_str = function
  | Guarded (expr, assigns) -> "guard: "^(expr_ast_to_str expr)^(List.fold_left (^) "\n  assigns:" (List.map assigns_to_str assigns))
  | Default assigns -> "default"
  | _ -> "existential";;

let fn_add (x, y) = Add (x, y);;
let fn_sub (x, y) = Sub (x, y);;
let fn_mul (x, y) = Mul (x, y);;
let fn_div (x, y) = Div (x, y);;
let fn_ge (x, y) = Ge (x, y);;
let fn_gt (x, y) = Gt (x, y);;
let fn_lt (x, y) = Le (x, y);;
let fn_le (x, y) = Lt (x, y);;
let fn_eq (x, y) = Eq (x, y);;
let fn_neq (x, y) = Neq (x, y);;
let fn_and (x, y) = And (x, y);;
let fn_or (x, y) = Or (x, y);;
let fn_xor (x, y) = Xor (x, y);;

let rec contains_cond = function
  | Cond (_, _) -> true
  | Add (e1, e2) -> (contains_cond e1) || (contains_cond e2)
  | Sub (e1, e2) -> (contains_cond e1) || (contains_cond e2)
  | Mul (e1, e2) -> (contains_cond e1) || (contains_cond e2)
  | Div (e1, e2) -> (contains_cond e1) || (contains_cond e2)
  | Gt (e1, e2) -> (contains_cond e1) || (contains_cond e2)
  | Ge (e1, e2) -> (contains_cond e1) || (contains_cond e2)
  | Lt (e1, e2) -> (contains_cond e1) || (contains_cond e2)
  | Le (e1, e2) -> (contains_cond e1) || (contains_cond e2)
  | Eq (e1, e2) -> (contains_cond e1) || (contains_cond e2)
  | Neq (e1, e2) -> (contains_cond e1) || (contains_cond e2)
  | And (e1, e2) -> (contains_cond e1) || (contains_cond e2)
  | Or (e1, e2) -> (contains_cond e1) || (contains_cond e2)
  | Xor (e1, e2) -> (contains_cond e1) || (contains_cond e2)
  | Implies (e1, e2) -> (contains_cond e1) || (contains_cond e2)
  | _ -> false;;

let rec non_toplevel_cond = function
  | Cond (ifs, els) -> List.fold_left (||) (contains_cond els) (List.map contains_cond (List.map fst ifs))
  | other -> contains_cond other;;

let rec conjunction ls =
  match ls with
  | l::l'::ls -> conjunction (And(l, l')::ls)
  | [res] -> res
  | _ -> False
and
(*
  given a list of conditions [c1; c2; c3; ...; cn],
  returns the list [ce; cn'; ... ; c3'; c2'; c1'],
  where c1', c2', ..., cn', ce are conditions such that
  the expression
  if c1 then e1 elif c2 then e2 elif ... elif cn then en else e
  is equivalent to
  if c1' then e1; if c2' then e2; ...; if cn' then en; if ce then e
*)
expand_conds conds =
  let rec ec prev conds res =
    (match conds with
    | [] -> ((conjunction (List.map (fun x -> Not x) prev)))::res
    | c::cs ->
        ec (c::prev) cs ((And (conjunction (List.map (fun x -> Not x) prev), c))::res)) in
  match conds with
   | [] -> []
   | c::cs -> ec [c] cs [c]
and
(* turn an i b_1 then b_2 else if ... then b_n-1 else b_n expression into a disjunction *)
flatten_cond_to_bool = function
  | Cond (ifs, els) ->
      let ls = List.rev_map2 (fun x y -> And(x, y)) (expand_conds (List.map fst ifs)) (els::(List.rev_map snd ifs)) in
        List.fold_left (fun x y -> flatten_cond (Or (x, y))) (List.hd ls) (List.tl ls)
  | other -> other
and
flattener cond = function
  | Cond (ifs, els) ->
      (* generate new ifs *)
      List.rev_map2 (fun x y -> (And(cond, x), y))
        (expand_conds (List.map fst ifs)) (els::(List.rev_map snd ifs))
  | other -> [(cond, other)]
and
pair_flattener (e1, e2) f =
  match (flatten_cond e1, flatten_cond e2) with
  | (Cond (ifs, els), e) ->
      let ifs' = List.map (fun (x, y) -> (x, f (y, e))) ifs in
      flatten_cond (Cond (ifs', f (e, els)))
  | (e, Cond (ifs, els)) ->
      let ifs' = List.map (fun (x, y) -> (x, f (e, y))) ifs in
      Cond (ifs', f (els, e))
  | (e1', e2') -> f (e1', e2')
and
(* flatten conditional statements in an expression so there is at most one conditional
in the expression (conditionals within logical expressions are converted
to logical expressions); simpler way? *)
flatten_cond = function
  | Cond (ifs, els) ->
      let res =
      let ifs' = List.map (fun (x, y) -> (flatten_cond x, flatten_cond y)) ifs in
      let els' = flatten_cond els in
      (* flatten the ifs *)
      let ifs'' = List.flatten (List.map2 flattener (List.map fst ifs') (List.map snd ifs')) in
      (* flatten the else *)
      (match els' with
      | Cond (e_ifs, e_els) ->
          Cond
            (List.map (fun (x, y) -> (flatten_cond (And(x, List.hd (expand_conds (List.map fst ifs'')))), y)) e_ifs,
             e_els)
      | _ -> Cond (ifs'', els')) in res
  (* arithmetic *)
  | Add (e1, e2) -> pair_flattener (e1, e2) fn_add
  | Sub (e1, e2) -> pair_flattener (e1, e2) fn_sub
  | Mul (e1, e2) -> pair_flattener (e1, e2) fn_mul
  | Div (e1, e2) -> pair_flattener (e1, e2) fn_div
  (* comparisons *)
  | Ge (e1, e2) -> pair_flattener (e1, e2) fn_ge
  | Gt (e1, e2) -> pair_flattener (e1, e2) fn_gt
  | Le (e1, e2) -> pair_flattener (e1, e2) fn_le
  | Lt (e1, e2) -> pair_flattener (e1, e2) fn_lt
  | Eq (e1, e2) -> pair_flattener (e1, e2) fn_eq
  | Neq (e1, e2) -> pair_flattener (e1, e2) fn_neq
  (* logical expressions *)
  | Not e ->
      (match flatten_cond e with
       | Cond (ifs, els) ->
           let ifs' = List.map (fun (x, y) -> (x, Not y)) ifs in
           Cond (ifs', Not els)
       | e' -> Not e')
  | And (e1, e2) -> pair_flattener (e1, e2) fn_and
  | Or (e1, e2) -> pair_flattener (e1, e2) fn_or
  | Xor (e1, e2) -> pair_flattener (e1, e2) fn_xor
  | Implies (e1, e2) -> 
      flatten_cond (Or (Not e1, e2))
  | Iff (e1, e2) ->
      flatten_cond
        (And (Or (Not e1, e2),
              Or (e1, Not e2)))
  | other -> other;;

let preproc_assign = function
  | Assign (e1, e2) -> Assign (e1, flatten_cond e2)
  | Member (e1, e2) -> Member (e1, flatten_cond e2);;

(* convert a guarded command with conditionals in its guard into separate guarded commands *)
let rec preproc_guarded_guard = function
  | Guarded (guard, assigns) ->
    (match flatten_cond guard with 
      | Cond (ifs, els) ->
          let conds = List.rev_map2 (fun x y -> And(x, y)) (expand_conds (List.map fst ifs)) (els::(List.rev_map snd ifs)) in
          List.map (fun c -> Guarded (c, assigns)) conds
      | other -> [Guarded (other, assigns)])
  | _ -> raise (Expected_guarded_command "as argument to preproc_guarded_guard");;

(* convert a guarded command with conditionals in its assignments into separate
guarded commands *)
let rec preproc_guarded_assigns = function
  | (Guarded (guard, finished)) -> (function
    | (Assign (e, Cond (ifs, els)))::rest ->
        let conds = expand_conds (List.map fst ifs) in
        let exprs = els::(List.rev_map snd ifs) in
        let guardeds =
          List.rev_map2
            (fun x y -> preproc_guarded_assigns
               (Guarded (And (guard, x), (Assign (e, y))::finished))
               rest)
            conds exprs in
        List.flatten guardeds
    | assign::assigns ->
        preproc_guarded_assigns (Guarded (guard, assign::finished)) assigns
    | [] -> [Guarded (guard, finished)])
  | _ -> raise (Expected_guarded_command "as argument to preproc_guarded_assigns");;

let rec preproc_guarded = function
  | ExistentialGuarded (decl, gc) -> raise (Unimplemented "Existential guards") (*List.map (fun gc -> ExistentialGuarded (decl, gc)) (preproc_guarded gc)*)
  | Guarded (guard, assigns) ->
      List.flatten (List.map preproc_guarded_guard (preproc_guarded_assigns (Guarded (guard, [])) (List.map preproc_assign assigns)))
  | other -> [other];;

let rec preproc_transition = function
  | NoTransition -> NoTransition
  | Assignments assigns ->
      (* if there are conditionals in the assignments, convert into guarded commands *)
      (match preproc_guarded (Guarded (True, assigns)) with
        | [Guarded (_, assigns)] -> Assignments assigns
        | gs -> GuardedCommands gs)
  | GuardedCommands gls ->
      let is_default = function
        | Default _ -> true
        | _ -> false in
      let gls' = List.flatten (List.map preproc_guarded gls) in
      let (ds, gs) = List.partition is_default gls' in
      (* handle ELSE *)
      match ds with
      | [] -> GuardedCommands gls'
      | [Default assigns] ->
          (* get explicit guard *)
          let g =
            List.hd (expand_conds (List.map
            (function (Guarded (g, a)) -> g | _ -> raise (Expected_guarded_command "as non-default elements"))
            gs)) in
          (* see if it is necessary to make guard explicit *)
          (match preproc_guarded (Guarded (g, assigns)) with
            | [Guarded (_, assigns)] -> GuardedCommands (gs @ [Default assigns]) (* it is not necessary *) 
            | gs' -> (* it is necessary *)
                (match split_at gs' (List.length gs' - 1) with
                 | (gs', [Guarded (_, default)]) -> GuardedCommands (gs @ gs' @ [Default default])
                 | _ -> raise (Expected_guarded_command "as sole element of second list")))
      | _ -> raise Duplicate_else_guarded_commands;;

let rec preproc_defs res = function
  | [] -> res
  | (Module_def (str, sal_mod))::ds ->
      preproc_defs
        ((Module_def (str, { sal_mod with
          transition = preproc_transition (sal_mod.transition) }))::res)
        ds
  | _::ds -> preproc_defs res ds;;
  
(*
let remove_existential_guards
  let remove_existential res id = function
    | ExistentialGuarded ((strs, st), gc) ->
      remove_existential (List.map (fun str -> Constant_decl (str^"*"^id, st))::res) id gc
    | _ -> res in
  let is_module = function
    | Module_def _ -> true
    | _ -> false in
  let modules = List.filter is_module ds in
*)   


let preproc sal_ctx =
  let ctx' = inline sal_ctx in
  printf "%s\n" "inlined";
  let defs = preproc_defs [] ctx'.definitions in
  { ctx' with definitions = defs };;
