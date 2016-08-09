open Simple_ast;;
open Mcmt_simple_ast;;
open Format;;

module StrMap = Map.Make(String);;

exception Unexpected_expression;;
exception Unexpected_declaration;;

let rec add_bindings map = function
  | (str, e)::eps -> add_bindings (StrMap.add str e map) eps
  | [] -> map

let rec apply_to_simple_ident f = function
  | Int i -> Int i
  | Float f -> Float f
  | Ident str -> f str
  | Add (e1, e2) -> Add (apply_to_simple_ident f e1, apply_to_simple_ident f e2)
  | Sub (e1, e2) -> Sub (apply_to_simple_ident f e1, apply_to_simple_ident f e2)
  | Mul (e1, e2) -> Mul (apply_to_simple_ident f e1, apply_to_simple_ident f e2)
  | Div (e1, e2) -> Div (apply_to_simple_ident f e1, apply_to_simple_ident f e2)
  | Ge (e1, e2) -> Ge (apply_to_simple_ident f e1, apply_to_simple_ident f e2)
  | Gt (e1, e2) -> Gt (apply_to_simple_ident f e1, apply_to_simple_ident f e2)
  | Eq (e1, e2) -> Eq (apply_to_simple_ident f e1, apply_to_simple_ident f e2)
  | Not e -> Not (apply_to_simple_ident f e)
  | And (e1, e2) -> And (apply_to_simple_ident f e1, apply_to_simple_ident f e2)
  | Or (e1, e2) -> Or (apply_to_simple_ident f e1, apply_to_simple_ident f e2)
  | Cond (e1, e2, e3) -> Cond (apply_to_simple_ident f e1, apply_to_simple_ident f e2, apply_to_simple_ident f e3)
  | Seq es -> Seq (List.map (apply_to_simple_ident f) es)
  | True -> True
  | False -> False
  | _ -> raise Unexpected_expression;;

let inline_simple map =
  apply_to_simple_ident
    (fun str ->
       if StrMap.mem str map
       then StrMap.find str map
       else Ident str);;

let rec contains_assign = function
  | Mcmt_ast.Assign (_, _) -> true
  | Mcmt_ast.And es -> List.fold_left (||) false (List.map contains_assign es)
  | Mcmt_ast.Or es -> List.fold_left (||) false (List.map contains_assign es)
  | _ -> false

let rec mcmt_to_expr map = function
  | Mcmt_ast.Int i -> Int i
  | Mcmt_ast.Real f -> Float f
  | Mcmt_ast.Next e ->
      apply_to_simple_ident (fun str -> Ident ("next."^str)) (mcmt_to_expr map e)
  | Mcmt_ast.Ident str ->
      if StrMap.mem str map
      then StrMap.find str map
      else Ident str
  | Mcmt_ast.Add (e1, e2) -> Add (mcmt_to_expr map e1, mcmt_to_expr map e2)
  | Mcmt_ast.Sub (e1, e2) -> Sub (mcmt_to_expr map e1, mcmt_to_expr map e2)
  | Mcmt_ast.Mul (e1, e2) -> Mul (mcmt_to_expr map e1, mcmt_to_expr map e2)
  | Mcmt_ast.Div (e1, e2) -> Div (mcmt_to_expr map e1, mcmt_to_expr map e2)
  | Mcmt_ast.Ge (e1, e2) -> Ge (mcmt_to_expr map e1, mcmt_to_expr map e2)
  | Mcmt_ast.Gt (e1, e2) -> Gt (mcmt_to_expr map e1, mcmt_to_expr map e2)
  | Mcmt_ast.Le (e1, e2) -> Ge (mcmt_to_expr map e2, mcmt_to_expr map e1)
  | Mcmt_ast.Lt (e1, e2) -> Gt (mcmt_to_expr map e2, mcmt_to_expr map e1)
  | Mcmt_ast.Eq (e1, e2) -> Eq (mcmt_to_expr map e1, mcmt_to_expr map e2)
  | Mcmt_ast.Neq (e1, e2) -> Not (Eq (mcmt_to_expr map e1, mcmt_to_expr map e2))
  | Mcmt_ast.And es ->
      if contains_assign (Mcmt_ast.And es)
      then Seq (List.map (mcmt_to_expr map) es)
      else
        (match es with
         | [e1; e2] -> And (mcmt_to_expr map e1, mcmt_to_expr map e2)
         | (e::es) -> And (mcmt_to_expr map e, mcmt_to_expr map (Mcmt_ast.And es))
         | _ -> raise Unexpected_expression)
  | Mcmt_ast.Or es ->
      if contains_assign (Mcmt_ast.Or es)
      then Branch (List.map (mcmt_to_expr map) es)
      else
        (match es with
         | [e1; e2] -> Or (mcmt_to_expr map e1, mcmt_to_expr map e2)
         | (e::es) -> Or (mcmt_to_expr map e, mcmt_to_expr map (Mcmt_ast.Or es))
         | _ -> raise Unexpected_expression)
(*
  | Mcmt_ast.Or [e1; e2] -> Or (mcmt_to_expr map e1, mcmt_to_expr map e2)
  | Mcmt_ast.Or (e::es) -> Or (mcmt_to_expr map e, mcmt_to_expr map (Mcmt_ast.Or es))
*)
  | Mcmt_ast.Xor (e1, e2) ->
      let (e1', e2') = (mcmt_to_expr map e1, mcmt_to_expr map e2) in
      Or ( And (e1', Not e2'), And (Not e1', e2') )
  | Mcmt_ast.Implies (e1, e2) ->
      Or ( Not (mcmt_to_expr map e1), mcmt_to_expr map e2)
  | Mcmt_ast.Not e -> Not (mcmt_to_expr map e)
  | Mcmt_ast.Ite (e1, e2, e3) -> Cond (mcmt_to_expr map e1, mcmt_to_expr map e2, mcmt_to_expr map e3)
  | Mcmt_ast.Let ((x, y)::es, e) ->
      let map' = StrMap.add x (mcmt_to_expr map y) map in
      mcmt_to_expr map' (Mcmt_ast.Let (es, e))
  | Mcmt_ast.Let ([], e) -> mcmt_to_expr map e
  | Mcmt_ast.Assign (e1, e2) -> Eq (mcmt_to_expr map e1, mcmt_to_expr map e2)
  | Mcmt_ast.True -> True
  | Mcmt_ast.False -> False;;

let to_simple_decl = function
  | Mcmt_ast.Int_decl str -> Int_decl str
  | Mcmt_ast.Real_decl str -> Real_decl str
  | Mcmt_ast.Bool_decl str -> Bool_decl str;;

let make_prefix pre = function
  | Int_decl str -> Int_decl (pre^"."^str)
  | Real_decl str -> Real_decl (pre^"."^str)
  | Bool_decl str -> Bool_decl (pre^"."^str)
  | _ -> raise Unexpected_declaration;;

let rec mcmt_defs_to_ts st_map expr_map ts = function
  | Mcmt_ast.State_type (str, svs, inputs)::ds -> mcmt_defs_to_ts (add_bindings st_map [(str, (svs, inputs))]) expr_map ts ds
  | Mcmt_ast.States (str, e1, e2)::ds -> mcmt_defs_to_ts st_map (add_bindings expr_map [(str, mcmt_to_expr expr_map e2)]) ts ds
  | Mcmt_ast.Transition (str, e1, e2)::ds -> printf "%s\n" "transition"; mcmt_defs_to_ts st_map (add_bindings expr_map [(str, mcmt_to_expr expr_map e2)]) ts ds
  | Mcmt_ast.Transition_system (str, Mcmt_ast.Ref st, init, trans)::ds ->
      let (svs, inputs) = StrMap.find st st_map in
      mcmt_defs_to_ts st_map expr_map ts (Mcmt_ast.Transition_system (str, Mcmt_ast.Anon (svs, inputs), init, trans)::ds)
  | Mcmt_ast.Transition_system (str, Mcmt_ast.Anon (svs, inputs), init, trans)::ds ->
      let name = str in
      let decls = List.map to_simple_decl inputs in
      let state_vars = List.map to_simple_decl svs in
      let current_sv_decls = state_vars in
      let next_sv_decls = List.map (make_prefix "next") state_vars in
      let init = mcmt_to_expr expr_map init in
      let trans = mcmt_to_expr expr_map trans in 
      mcmt_defs_to_ts st_map expr_map (StrMap.add name { name; decls; current_sv_decls; next_sv_decls; init; trans; invs = [] } ts) ds
  | Mcmt_ast.Constant (str, e)::ds -> mcmt_defs_to_ts st_map (add_bindings expr_map [(str, mcmt_to_expr expr_map e)]) ts ds
  | Mcmt_ast.Assert (str, e)::ds ->
      let e' = mcmt_to_expr expr_map e in
      if StrMap.mem str ts
      then
        let system = StrMap.find str ts in
          mcmt_defs_to_ts st_map expr_map (StrMap.add str {system with invs = e'::system.invs} ts) ds
      else
        mcmt_defs_to_ts st_map expr_map ts ds
  | Mcmt_ast.Query (_, _)::ds -> mcmt_defs_to_ts st_map expr_map ts ds
  | [] -> ts;;

let mcmt_to_ts mcmt_defs =
  mcmt_defs_to_ts StrMap.empty StrMap.empty StrMap.empty mcmt_defs
  |> StrMap.bindings
  |> List.map snd;;
