open Ast.Sal_ast;;
open Format;;

(* Inline functions, constant declarations, let-statements *)
module StrMap = Map.Make(String)

exception Function_definition_not_found of string
exception Wrong_definition_type_found of string
exception Cannot_pair_keys_and_values;;

type to_inline = Type of sal_type | Val of sal_expr | Fun of string list * sal_expr

let rec add_kvs ctx = function
  | ([],[]) -> ctx 
  | (k::ks, v::vs) -> add_kvs (StrMap.add k (Val v) ctx) (ks, vs)
  | _ -> raise Cannot_pair_keys_and_values;;

let rec inline_expr ctx = function
  | Ident str ->
      if StrMap.mem str ctx
      then (match StrMap.find str ctx with
          | Val (Ident str) -> Ident str
          | Val expr -> inline_expr ctx expr
          | _ -> raise (Wrong_definition_type_found ("Expected sal_expr for "^str)))
      else Ident str
  | Funcall (str, es) ->
      if StrMap.mem str ctx
      then (match StrMap.find str ctx with
        | Fun (strs, expr) ->
          inline_expr (add_kvs ctx (strs, es)) expr
        | _ -> raise (Wrong_definition_type_found ("Expected function for "^str)))
      else Funcall (str, es) (* raise (Function_definition_not_found (str)) *)
  | Array_access (e1, e2) ->
      Array_access (e1, inline_expr ctx e2)
  | Array_literal (str, st, e) ->
      Array_literal (str, inline_type ctx st, inline_expr ctx e)
  | Set_literal (str, st, e) ->
      Set_literal (str, inline_type ctx st, inline_expr ctx e)
  | SSet_cardinal (str, st, e) ->
      SSet_cardinal (str, inline_type ctx st, inline_expr ctx e)
  | Cond (ifs, els) ->
      Cond
        (List.map (fun (e1, e2) -> (inline_expr ctx e1, inline_expr ctx e2)) ifs,
        inline_expr ctx els)
  | Opp e        -> Opp (inline_expr ctx e)
  | Add (e1, e2) -> Add (inline_expr ctx e1, inline_expr ctx e2)
  | Sub (e1, e2) -> Sub (inline_expr ctx e1, inline_expr ctx e2)
  | Mul (e1, e2) -> Mul (inline_expr ctx e1, inline_expr ctx e2)
  | Div (e1, e2) -> Div (inline_expr ctx e1, inline_expr ctx e2)
  | Ge (e1, e2)  -> Ge  (inline_expr ctx e1, inline_expr ctx e2)
  | Gt (e1, e2)  -> Gt  (inline_expr ctx e1, inline_expr ctx e2)
  | Le (e1, e2)  -> Le  (inline_expr ctx e1, inline_expr ctx e2)
  | Lt (e1, e2)  -> Lt  (inline_expr ctx e1, inline_expr ctx e2)
  | Eq (e1, e2)  -> Eq  (inline_expr ctx e1, inline_expr ctx e2)
  | Neq (e1, e2) -> Neq (inline_expr ctx e1, inline_expr ctx e2)
  | Not e        -> Not (inline_expr ctx e)
  | And (e1, e2) -> And (inline_expr ctx e1, inline_expr ctx e2)
  | Or (e1, e2)  -> Or  (inline_expr ctx e1, inline_expr ctx e2)
  | Xor (e1, e2) -> Xor (inline_expr ctx e1, inline_expr ctx e2)
  | Implies (e1, e2) -> Implies (inline_expr ctx e1, inline_expr ctx e2)
  | Iff (e1, e2) -> Iff (inline_expr ctx e1, inline_expr ctx e2)
  | Exists (decls, e) -> Exists (decls, inline_expr ctx e)
  | Forall (decls, e) -> Forall (decls, inline_expr ctx e)
  | Let (decls, e) ->
      let strs = List.map (fun (str, _, _) -> str) decls in
      let exprs = List.map (fun (_, _, expr) -> expr) decls in
      inline_expr (add_kvs ctx (strs, exprs)) e
  | other -> other
and inline_type ctx = function
  | Base_type str ->
      if StrMap.mem str ctx
      then (match StrMap.find str ctx with
        | Type st -> inline_type ctx st
        | _ -> raise (Wrong_definition_type_found ("Expected sal_type for "^str)))
      else Base_type str
  | Range (e1, e2) ->
      Range (inline_expr ctx e1, inline_expr ctx e2)
  | Array (st1, st2) ->
      Array (inline_type ctx st1, inline_type ctx st2)
  | Subtype (str, st, expr) ->
      Subtype (str, inline_type ctx st, inline_expr ctx expr)
  | other -> other;;

let inline_assignment ctx = function
  | Assign (e1, e2) -> Assign (inline_expr ctx e1, inline_expr ctx e2)
  | Member (e1, e2) -> Member (inline_expr ctx e1, inline_expr ctx e2);;

let rec inline_guarded_commands ctx = function
  | ExistentialGuarded (decl, gc) -> ExistentialGuarded (decl, inline_guarded_commands ctx gc)
  | Guarded (e, assignments) ->
      Guarded (inline_expr ctx e, List.map (inline_assignment ctx) assignments)
  | Default assignments -> Default (List.map (inline_assignment ctx) assignments);;

let inline_transition ctx = function
  | Assignments ls -> Assignments (List.map (inline_assignment ctx) ls)
  | GuardedCommands gcs -> GuardedCommands (List.map (inline_guarded_commands ctx) gcs)
  | other -> other;;

let rec inline_defs ctx res = function
  | [] -> res
  | (Type_def (str, st))::ds -> inline_defs (StrMap.add str (Type st) ctx) res ds
  | (Constant_decl (str, st))::ds -> inline_defs ctx (Constant_decl(str, inline_type ctx st)::res) ds
  | (Constant_def (str, st, expr))::ds -> inline_defs (StrMap.add str (Val (inline_expr ctx expr)) ctx) res ds
  | (Function_def (str, sdl, st, expr))::ds ->
      inline_defs (StrMap.add str (Fun (List.flatten (List.map fst sdl), inline_expr ctx expr)) ctx) res ds
  | (Assertion (str1, tag, str2, expr))::ds ->
      inline_defs ctx (Assertion(str1, tag, str2, inline_expr ctx expr)::res) ds
  | (Module_def (str, sal_mod))::ds ->
      inline_defs ctx
        (Module_def (str, { sal_mod with
          initialization = List.map (inline_assignment ctx) (sal_mod.initialization);
          definition = List.map (inline_assignment ctx) (sal_mod.definition);
          invariant =
            ( match sal_mod.invariant with
              | Some e -> Some (inline_expr ctx e)
              | None -> None );
          transition = inline_transition ctx (sal_mod.transition) })::res)
        ds
  | other -> other;;
  
let inline sal_ctx =
  let defs = inline_defs StrMap.empty [] sal_ctx.definitions in
  { sal_ctx with definitions = List.rev defs };;
