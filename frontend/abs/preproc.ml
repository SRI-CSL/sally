open Ast.Sal_ast;;
open Inline;;
open Format;;

(* call inline function and remove conditional expressions *)

let rec cond_ast_to_str ast =
  match ast with
  | And(e1, e2) -> "and("^(cond_ast_to_str e1)^", "^(cond_ast_to_str e2)^")"
  | Or(e1, e2) -> "or("^(cond_ast_to_str e1)^", "^(cond_ast_to_str e2)^")"
  | Not e -> "not("^(cond_ast_to_str e)^")"
  | True -> "true"
  | False -> "false"
  | _ -> "expr"

let rec conjunction ls =
  match ls with
  | l::l'::ls -> conjunction (And(l, l')::ls)
  | [res] -> res;;

let expand_conds conds =
  let rec ec prev conds res =
    (match conds with
    | [] -> (conjunction (List.map (fun x -> Not x) prev))::res
    | c::cs ->
        ec (c::prev) cs ((And (conjunction (List.map (fun x -> Not x) prev), c))::res)) in
  match conds with
   | [] -> []
   | c::cs -> ec [c] cs [c];;

(* turn an i b_1 then b_2 else if ... then b_n-1 else b_n expression into a disjunction *)
let flatten_cond ifs els =
  let ls = List.rev_map2 (fun x y -> And(x, y)) (expand_conds (List.map fst ifs)) (els::(List.rev_map snd ifs)) in
  let res = List.fold_left (fun x y -> Or (x, y)) (List.hd ls) (List.tl ls) in
  printf "flat: %s@." (cond_ast_to_str res); res;;

let rec preproc_guarded_guard (Guarded (guard, assigns)) =
  match guard with 
    | Cond (ifs, els) -> (* convert a guarded command with conditionals in its guard into separate guarded commands *)
        let conds = List.rev_map2 (fun x y -> And(x, y)) (expand_conds (List.map fst ifs)) (els::(List.rev_map snd ifs)) in
        List.map (fun c -> Guarded (c, assigns)) conds
    | other -> [Guarded (other, assigns)];;

(* convert a guarded command with conditionals in its assignments into separate
guarded commands *)
let rec preproc_guarded_assigns (Guarded (guard, finished)) = function
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
  | [] -> [Guarded (guard, finished)];;

let rec preproc_guarded = function
  | ExistentialGuarded (decl, gc) -> List.map (fun gc -> ExistentialGuarded (decl, gc)) (preproc_guarded gc)
  | Guarded (guard, assigns) ->
      (List.map (fun (Guarded (g, a)) -> preproc_guarded_assigns (Guarded (g, [])) a)
               (preproc_guarded_guard (Guarded (guard, assigns))))
      |> List.flatten
  | other -> [other];;

let rec preproc_transition st =
  match st with
  | NoTransition -> NoTransition
  | Assignments assigns ->
      (match preproc_guarded_assigns (Guarded (True, [])) assigns with
        | [g] -> Assignments assigns
        | gs -> GuardedCommands gs)
  | GuardedCommands gls ->
      GuardedCommands (List.flatten (List.map preproc_guarded gls));;

let rec preproc_defs ds res =
  match ds with
  | [] -> res
  | (Module_def (str, sal_mod))::ds ->
      preproc_defs ds
        ((Module_def (str, { sal_mod with
          transition = preproc_transition (sal_mod.transition) }))::res)
  | _::ds -> preproc_defs ds res;;
  
let preproc sal_ctx =
  let ctx' = inline sal_ctx in
  let defs = preproc_defs ctx'.definitions [] in
  { ctx' with definitions = defs };;
