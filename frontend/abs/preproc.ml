open Ast.Sal_ast;;


let preproc_def d =
  match d with
  | Constant_def (str, st, expr) ->
  | Function_def (str, st, expr) ->
  | Module_def (str, sal_mod) ->
      { sal_mod with
          initialization = preproc_assignments (sal_mod.initialization);
          definition = preproc_assignments (sal_mod.definition);
          invariant =
            ( match sal_mod.invariant with
              | Some e -> preproc_expression e
              | None -> None );
          transition = preproc_transition (sal_mod.transition) };;
