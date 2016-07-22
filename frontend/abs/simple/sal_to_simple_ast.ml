open Ast;;
open Simple_ast;;

exception Unexpected_expr;;
exception Unimplemented of string;;

let rec sal_to_expr = function
  | Sal_ast.Decimal i    -> Int i
  | Sal_ast.Float f      -> Float f
  | Sal_ast.Ident str    -> Ident str
  | Sal_ast.Cond ((e1, e2)::ifs, els) ->
      Cond
        (sal_to_expr e1,
         sal_to_expr e2,
         sal_to_expr (Sal_ast.Cond (ifs, els)))
  | Sal_ast.Cond ([], els) -> sal_to_expr els
  | Sal_ast.Add (e1, e2) -> Add (sal_to_expr e1, sal_to_expr e2)
  | Sal_ast.Sub (e1, e2) -> Sub (sal_to_expr e1, sal_to_expr e2)
  | Sal_ast.Mul (e1, e2) -> Mul (sal_to_expr e1, sal_to_expr e2)
  | Sal_ast.Div (e1, e2) -> Div (sal_to_expr e1, sal_to_expr e2)
  | Sal_ast.Ge (e1, e2)  -> Ge (sal_to_expr e1, sal_to_expr e2)
  | Sal_ast.Gt (e1, e2)  -> Gt (sal_to_expr e1, sal_to_expr e2)
  | Sal_ast.Le (e1, e2)  -> Ge (sal_to_expr e2, sal_to_expr e1)
  | Sal_ast.Lt (e1, e2)  -> Gt (sal_to_expr e2, sal_to_expr e1)
  | Sal_ast.Eq (e1, e2)  -> Eq (sal_to_expr e1, sal_to_expr e2)
  | Sal_ast.Neq (e1, e2) -> Neq (sal_to_expr e1, sal_to_expr e2)
  | Sal_ast.Not e        -> Not (sal_to_expr e)
  | Sal_ast.And (e1, e2) -> And (sal_to_expr e1, sal_to_expr e2)
  | Sal_ast.Or  (e1, e2) -> Or (sal_to_expr e1, sal_to_expr e2)
  | Sal_ast.Xor (e1, e2) -> 
      let (e1', e2') = (sal_to_expr e1, sal_to_expr e2) in
      Or (And (e1', Not e2'), And (Not e1', e2'))
  | Sal_ast.Implies (e1, e2) -> Or (Not (sal_to_expr e1), sal_to_expr e2)
  | Sal_ast.Iff (e1, e2) ->
      let (e1', e2') = (sal_to_expr e1, sal_to_expr e2) in
      And (Or (Not e1', e2'), Or (e1', Not e2'))
  | Sal_ast.True         -> True
  | Sal_ast.False        -> False
  | _                    -> raise Unexpected_expr;;

let rec convert_sal_assignment = function
  | Sal_ast.Assign (e1, e2) -> Assign (sal_to_expr e1, sal_to_expr e2)
  | _ -> raise (Unimplemented "member");;

let rec convert_sal_guardeds res = function
  | [] -> (res, None)
  | Sal_ast.ExistentialGuarded (_, _)::gs -> raise (Unimplemented "existential guarded commands")
  | Sal_ast.Guarded (e, assigns)::gs -> convert_sal_guardeds ((sal_to_expr e, List.map convert_sal_assignment assigns)::res) gs
  | [Sal_ast.Default assigns] -> (res, Some (List.map convert_sal_assignment assigns))
  | _ -> raise Unexpected_expr;;

let convert_sal_transition = function
  | Sal_ast.NoTransition -> None
  | Sal_ast.Assignments assigns ->
      Some ([(True, List.map convert_sal_assignment assigns)], None)
  | Sal_ast.GuardedCommands gcs ->
      Some (convert_sal_guardeds [] gcs);;

let sal_to_decl str = function
  | Sal_ast.Base_type("NATURAL") -> Nat_decl str
  | Sal_ast.Base_type("INTEGER") -> Int_decl str
  | Sal_ast.Base_type("REAL")    -> Real_decl str
  | _ -> raise (Unimplemented "Non-numerical type declarations");;

let sal_to_progs ctx =
  let defs = ctx.Sal_ast.definitions in
  let rec to_prog constants = function
    | [] -> raise (Unimplemented "No module")
    | (Sal_ast.Constant_decl (str, st))::ds -> to_prog (sal_to_decl str st::constants) ds
    | (Sal_ast.Module_def (str, sm))::ds ->
        (match convert_sal_transition sm.Sal_ast.transition with
        | Some (guarded, default) ->
            { constants;
              state_vars =
                List.flatten (List.map (fun x -> List.map (fun y -> sal_to_decl y (snd x)) (fst x)) (List.flatten (List.map snd sm.Sal_ast.state_vars)));
              invariants = []; guarded; default }
        | None -> raise (Unimplemented "No transition"))
    | (Sal_ast.Assertion (_,_,_,_))::ds -> raise (Unimplemented "Assertion preceding module")
    | _ -> raise (Unimplemented "Other type of sal_def") in
  to_prog [] defs;;

  
