(* Create abstract program from simple program *)
open Simple_ast;;
open Apron;;
open Format;;

exception Unimplemented of string;;

let from_decls ds =
  (* go through the decl list and collect the nat, int, and float variables *)
  let rec get_vars nats ints floats = function
    | [] -> (nats, ints, floats)
    | Simple_ast.Nat_decl n::ds -> get_vars (Var.of_string n::nats) ints floats ds
    | Simple_ast.Int_decl i::ds -> get_vars nats (Var.of_string i::ints) floats ds
    | Simple_ast.Real_decl f::ds -> get_vars nats ints (Var.of_string f::floats) ds in
  (* create the constraint nat >= 0 for a given variable nat in the environment env *)
  let get_nat_constraints env nat =
    let linexpr = Linexpr1.make env in
    Linexpr1.set_coeff linexpr nat (Coeff.Scalar (Scalar.of_int 1));
    Linexpr1.set_cst linexpr (Coeff.Scalar (Scalar.of_int 0));
    Lincons1.make linexpr Lincons1.SUPEQ in
  let (nats, ints, floats) = get_vars [] [] [] ds in
  let env = Environment.make (Array.of_list (nats @ ints)) (Array.of_list floats) in
  let invs = List.map (get_nat_constraints env) nats in
  (env, invs);;

(*
let rec from_expr man env = function
  | Simple_ast.Nat n -> Val (Coeff.Scalar (Scalar.of_int n))
  | Simple_ast.Int i -> Val (Coeff.Scalar (Scalar.of_int i))
  | Simple_ast.Float f -> Val (Coeff.Scalar (Scalar.of_float f))
  | Simple_ast.Ident str -> Ident str
  | Simple_ast.Add (e1, e2) -> Add ((from_expr man env e1, from_expr man env e2), None)
  | Simple_ast.Sub (e1, e2) -> Sub ((from_expr man env e1, from_expr man env e2), None)
  | Simple_ast.Mul (e1, e2) -> Mul ((from_expr man env e1, from_expr man env e2), None)
  | Simple_ast.Div (e1, e2) -> Div ((from_expr man env e1, from_expr man env e2), None)
  | Simple_ast.Ge (e1, e2) -> Ge ((from_expr man env e1, from_expr man env e2), None)
  | Simple_ast.Gt (e1, e2) -> Gt ((from_expr man env e1, from_expr man env e2), None)
  | Simple_ast.Eq (e1, e2) -> Eq ((from_expr man env e1, from_expr man env e2), None)
  | Simple_ast.Neq (e1, e2) -> Neq ((from_expr man env e1, from_expr man env e2), None)
  | Simple_ast.Not e -> Not (from_expr man env e, None)
  | Simple_ast.And (e1, e2) -> And ((from_expr man env e1, from_expr man env e2), None)
  | Simple_ast.Or (e1, e2) -> Or ((from_expr man env e1, from_expr man env e2), None)
  | Simple_ast.Assign (e1, e2) -> Assign ((from_expr man env e1, from_expr man env e2), None)
  | Simple_ast.Cond (e1, e2, e3) ->
      Cond ((from_expr man env e1, from_expr man env e2, from_expr man env e3), None)
  | Simple_ast.True -> True
  | Simple_ast.False -> False;;
*)

let rec arith_to_texpr man ctx v is_int binop e1 e2 =
  let v1 = Var.of_string ((Var.to_string v)^"_l") in
  let v2 = Var.of_string ((Var.to_string v)^"_r") in
  (* Solve branches recursively *)
  let abs_e1 = from_expr man ctx v1 e1 in
  let abs_e2 = from_expr man ctx v2 e2 in
  let abs = Abstract1.unify man abs_e1 abs_e2 in
  let env =
    if is_int
    then Environment.add (abs.Abstract1.env) [|v|] [||]
    else Environment.add (abs.Abstract1.env) [||] [|v|] in
  let abs = Abstract1.change_environment man abs env false in
  let typ = (* more options exist *)
    if is_int
    then Texpr1.Int
    else Texpr1.Real in
  (* The expression for applying the operator - need to resolve rounding *)
  let texpr =
    Texpr1.of_expr (abs.Abstract1.env)
      (Texpr1.Binop (binop, Texpr1.Var v1, Texpr1.Var v2, typ, Texpr1.Rnd)) in
  (* The new environment *)
  (abs, texpr)
and
arith_from_expr man ctx v is_int binop e1 e2 =
  let (abs, texpr) = arith_to_texpr man ctx v is_int binop e1 e2 in
  (* The assignment of the variable v to the texpr in the new environment *)
  Abstract1.assign_texpr man abs v texpr None
and
comp_from_expr man ctx v typ e1 e2 =
  (* get e1 - e2 *)
  let (abs, texpr) = arith_to_texpr man ctx v false Texpr1.Sub e1 e2 in
  (* now make e1 - e2 typ 0 constraint *)
  let tcons = Tcons1.make texpr typ in
  let tcons_arr = Tcons1.array_make abs.Abstract1.env 1 in
  Tcons1.array_set tcons_arr 0 tcons;
  Abstract1.meet_tcons_array man abs tcons_arr
(*
  Abstract1.change_environment man (Abstract1.meet_tcons_array man abs tcons_arr) (ctx.Abstract1.env) false*)
and
from_expr man ctx v = function
  | Nat n ->
      let env = Environment.add (ctx.Abstract1.env) [|v|] [||] in
      Abstract1.change_environment_with man ctx env false;
      Abstract1.assign_texpr man ctx v (Texpr1.of_expr (ctx.Abstract1.env) (Texpr1.Cst (Coeff.Scalar (Scalar.of_int n)))) None
  | Int i -> Abstract1.assign_texpr man ctx v (Texpr1.of_expr (ctx.Abstract1.env) (Texpr1.Cst (Coeff.Scalar (Scalar.of_int i)))) None
  | Float f -> Abstract1.assign_texpr man ctx v (Texpr1.of_expr (ctx.Abstract1.env) (Texpr1.Cst (Coeff.Scalar (Scalar.of_float f)))) None
  | Ident e -> Abstract1.assign_texpr man ctx v (Texpr1.of_expr (ctx.Abstract1.env) (Texpr1.Var (Var.of_string e))) None
  | Add (e1, e2) -> arith_from_expr man ctx v false Texpr1.Add e1 e2
  | Sub (e1, e2) -> arith_from_expr man ctx v false Texpr1.Sub e1 e2
  | Mul (e1, e2) -> arith_from_expr man ctx v false Texpr1.Mul e1 e2
  | Div (e1, e2) -> arith_from_expr man ctx v false Texpr1.Div e1 e2
  | Ge (e1, e2) -> comp_from_expr man ctx v Tcons1.SUPEQ e1 e2
  | Gt (e1, e2) -> comp_from_expr man ctx v Tcons1.SUP e1 e2
  | Eq (e1, e2) -> comp_from_expr man ctx v Tcons1.EQ e1 e2
  | Neq (e1, e2) -> comp_from_expr man ctx v Tcons1.DISEQ e1 e2
  | Not e -> raise (Unimplemented "Not")
(*
  | And (e1, e2) ->
      let v_str = Var.to_string v in
      (match (from_expr man env (Var.of_string (v_str^"_l")) e1, from_expr man env (Var.of_string(v_str^"_r")) e2) with
      | (Abs a1, Abs a2) -> Abs (Abstract1.unify man a1 a2)
      | _ -> raise (Unimplemented "No booleans"))
  | Or (e1, e2) ->
      let v_str = Var.to_string v in
      (match (from_expr man env (Var.of_string (v_str^"_l")) e1, from_expr man env (Var.of_string(v_str^"_r")) e2) with
      | (Abs a1, Abs a2) -> Abs (Abstract1.join man a1 a2)
      | _ -> raise (Unimplemented "booleans"))
*)
(*
  | Cond (e1, e2, e3) ->
      (match from_expr man env (Var.of_string (v_str^"if")) e1 with
      | Abs cond ->
          if (Abstract1.is_top cond)
          then from_expr man env v e2
          else if (Abstract1.is_bottom cond)
          then from_expr man env v e3
          else
            let v_str = Var.to_string v in
            let v1 = Var.of_string (v^"_l") in
            let v2 = Var.of_string (v^"_r") in
            (* expand using ctx later *)
            (match (from_expr man env v1 e1, from_expr man env v e2) with
             | (Abs a1
      | _ -> raise (Unimplemented "booleans"))
  *)   
  | _ -> raise (Unimplemented "Assign");;
      
let simple_to_abs man p =
  let (env, invs') = from_decls p.Simple_ast.decls in
  let invs = invs' in
  let exprs = List.map (from_expr man (Abstract1.top man env) (Var.of_string "tmp")) p.exprs in
  List.hd exprs;;
