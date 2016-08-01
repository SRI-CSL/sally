open Ast;;
open Simple_ast;;
open Format;;

exception Unexpected_expr;;
exception Unexpected_subtype_expression;;
exception Unimplemented of string;;

let rec replace_var lit repl =
  function
  | Ident e -> if e = lit then repl else Ident e
  | Add (e1, e2) -> Add (replace_var lit repl e1, replace_var lit repl e2)
  | Sub (e1, e2) -> Sub (replace_var lit repl e1, replace_var lit repl e2)
  | Mul (e1, e2) -> Mul (replace_var lit repl e1, replace_var lit repl e2)
  | Div (e1, e2) -> Div (replace_var lit repl e1, replace_var lit repl e2)
  | Ge (e1, e2) -> Ge (replace_var lit repl e1, replace_var lit repl e2)
  | Gt (e1, e2) -> Gt (replace_var lit repl e1, replace_var lit repl e2)
  | Eq (e1, e2) -> Eq (replace_var lit repl e1, replace_var lit repl e2)
  | Not e -> Not (replace_var lit repl e)
  | And (e1, e2) -> And (replace_var lit repl e1, replace_var lit repl e2)
  | Or (e1, e2) -> Or (replace_var lit repl e1, replace_var lit repl e2)
  | Cond (e1, e2, e3) -> Cond (replace_var lit repl e1, replace_var lit repl e2, replace_var lit repl e3)
  | Assign (_, _) -> raise Unexpected_subtype_expression
  | Seq _ -> raise Unexpected_subtype_expression
  | other -> other

let rec sal_to_expr = function
  | Sal_ast.Decimal i    -> Int i
  | Sal_ast.Float f      -> Float f
  | Sal_ast.Ident str    -> Ident str
  | Sal_ast.Set_literal (str, st, e) ->
      printf "set literal: %s\n" str;
      printf "set expr: %s\n" (Print_simple.string_of_simple (sal_to_expr e));
      printf "set expr applied: %s\n" (Print_simple.string_of_simple (replace_var str (Ident "expr") (sal_to_expr e)));
      Constrained (fun x -> replace_var str x (sal_to_expr e))
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
  | Sal_ast.Neq (e1, e2) -> Not (Eq (sal_to_expr e1, sal_to_expr e2))
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

let rec convert_sal_assignments next_state assigned assigns = function
  | [] ->
      let unassigned = List.filter (fun x -> not (List.mem x assigned)) next_state in
      (List.map (fun x -> Assign (Ident x, Ident (String.sub x 0 (String.length x - 1)))) unassigned) @ assigns
  | (Sal_ast.Assign (Sal_ast.Ident v, e))::asgns -> convert_sal_assignments next_state (v::assigned) (Assign (Ident v, sal_to_expr e)::assigns) asgns
  | (Sal_ast.Member (Sal_ast.Ident v, e))::asgns -> convert_sal_assignments next_state (v::assigned) (Assign (Ident v, sal_to_expr e)::assigns) asgns
  | _ -> raise Unexpected_expr;;

let rec convert_sal_guardeds next_state res = function
  | [] -> (List.map (fun (x, y) -> (x, Seq y)) res, None)
  | Sal_ast.ExistentialGuarded (_, _)::gs -> raise (Unimplemented "existential guarded commands")
  | Sal_ast.Guarded (e, assigns)::gs ->
      convert_sal_guardeds next_state ((sal_to_expr e, convert_sal_assignments next_state [] [] assigns)::res) gs
  | [Sal_ast.Default assigns] ->
      (List.map (fun (x, y) -> (x, Seq y)) res, Some (Seq (convert_sal_assignments next_state [] [] assigns)))
  | _ -> raise Unexpected_expr;;

let convert_sal_transition next_state = function
  | Sal_ast.NoTransition -> Some ([(True, Seq (convert_sal_assignments next_state [] [] []))], None)
  | Sal_ast.Assignments assigns ->
      Some ([(True, Seq (convert_sal_assignments next_state [] [] assigns))], None)
  | Sal_ast.GuardedCommands gcs ->
      Some (convert_sal_guardeds next_state [] gcs);;


let rec sal_to_decl str = function
  | Sal_ast.Base_type ("NATURAL") -> Nat_decl str
  | Sal_ast.Base_type ("INTEGER") -> Int_decl str
  | Sal_ast.Base_type ("REAL")    -> Real_decl str
  | Sal_ast.Base_type ("BOOLEAN") -> Bool_decl str
  | Sal_ast.Base_type (enum) -> Enum_decl (str, enum)
  | Sal_ast.Subtype (lit, st, expr) -> Constraint_decl (sal_to_decl str st, sal_to_expr expr |> replace_var lit (Ident str))
  | Sal_ast.Range (low, high) ->
      (* todo: find type; for now default to Real *)
      Constraint_decl (Real_decl str, And (Ge (Ident str, sal_to_expr low), Ge (sal_to_expr high, Ident str)))
  | Sal_ast.Array (_, st) -> raise (Unimplemented "Array type declarations")
  | Sal_ast.Enum _ -> raise (Unimplemented "Direct enum type declarations")
  | Sal_ast.Process -> raise (Unimplemented "Process type declarations")
  | Sal_ast.Process_type _ -> raise (Unimplemented "Process_type type declarations");;

(* Go through a preprocessed SAL AST and convert the first module into a simple program representation of the SAL program *)
let sal_to_progs ctx =
  let defs = ctx.Sal_ast.definitions in
  printf "%s\n" "to_progs";
  let rec to_prog constants = function
    | [] -> raise (Unimplemented "No module")
    | (Sal_ast.Type_def (str, Sal_ast.Enum strs))::ds ->
        to_prog (Enum_def (str, strs)::constants) ds
    | (Sal_ast.Constant_decl (str, st))::ds ->
        to_prog (sal_to_decl str st::constants) ds
    | (Sal_ast.Module_def (str, sm))::ds ->
        let svs = List.map snd sm.Sal_ast.state_vars |> List.flatten in
        let state_vars =
          List.flatten (List.map (fun x -> List.map (fun y -> sal_to_decl y (snd x)) (fst x)) svs) in
        let next_state_names = List.map (fun x -> x^"'") ((List.map fst svs) |> List.flatten) in
        let next_state_vars =
          List.flatten (List.map (fun x -> List.map (fun y -> sal_to_decl (y^"'") (snd x)) (fst x)) svs) in
        let no_transition = Seq (convert_sal_assignments next_state_names [] [] []) in
        (match convert_sal_transition next_state_names sm.Sal_ast.transition with
        | Some (guarded, default) ->
            { constants;
              invariants = [];
              state_vars;
              next_state_vars;
              initials = Seq (convert_sal_assignments [] [] [] sm.Sal_ast.initialization);
              guarded; default; no_transition }
        | None -> raise (Unimplemented "No transition"))
    | (Sal_ast.Assertion (_,_,_,_))::ds -> raise (Unimplemented "Assertion preceding module")
    | _ -> raise (Unimplemented "Other type of sal_def") in
  to_prog [] defs;;

  
