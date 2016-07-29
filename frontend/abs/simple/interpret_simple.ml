(* Interpret simple program *)
open Simple_ast;;
open Bddapron;;
open Bddapron.Syntax;;
open Apron;;
open Format;;

exception Unimplemented of string;;
exception Unexpected_expression;;

let rec make_bool_expr env cond binop e1 e2 =
  let e1' = Expr1.Bool.of_expr (make_expr1 env cond e1) in
  let e2' = Expr1.Bool.of_expr (make_expr1 env cond e2) in
  Expr1.Bool.to_expr (binop cond e1' e2')

and

make_apron_comp env cond cmp e =
  let e' = Expr1.Apron.of_expr (make_expr1 env cond e) in
  Expr1.Bool.to_expr (cmp cond e')

and

make_expr1 env cond = function
  | Nat e -> make_expr1 env cond (Int e)
  | Int e -> Expr1.Apron.to_expr (Expr1.Apron.cst env cond (Coeff.Scalar (Scalar.of_int e)))
  | Float e -> Expr1.Apron.to_expr (Expr1.Apron.cst env cond (Coeff.Scalar (Scalar.of_float e)))
  | Ident e -> Expr1.var env cond e
  | Add (e1, e2) ->
      let e1' = Expr1.Apron.of_expr (make_expr1 env cond e1) in
      let e2' = Expr1.Apron.of_expr (make_expr1 env cond e2) in
      Expr1.Apron.to_expr (Expr1.Apron.add cond e1' e2')
  | Sub (e1, e2) ->
      let e1' = Expr1.Apron.of_expr (make_expr1 env cond e1) in
      let e2' = Expr1.Apron.of_expr (make_expr1 env cond e2) in
      Expr1.Apron.to_expr (Expr1.Apron.sub cond e1' e2')
  | Mul (e1, e2) ->
      let e1' = Expr1.Apron.of_expr (make_expr1 env cond e1) in
      let e2' = Expr1.Apron.of_expr (make_expr1 env cond e2) in
      Expr1.Apron.to_expr (Expr1.Apron.mul cond e1' e2')
  | Div (e1, e2) ->
      let e1' = Expr1.Apron.of_expr (make_expr1 env cond e1) in
      let e2' = Expr1.Apron.of_expr (make_expr1 env cond e2) in
      Expr1.Apron.to_expr (Expr1.Apron.div cond e1' e2')
  | Ge (e1, e2) -> make_apron_comp env cond Expr1.Apron.supeq (Sub (e1, e2))
  | Gt (e1, e2) -> make_apron_comp env cond Expr1.Apron.sup (Sub (e1, e2))
  | Eq (e1, e2) ->
      let e1' = make_expr1 env cond e1 in
      let e2' = make_expr1 env cond e2 in
      let t1 = Expr1.typ_of_expr e1' in
      let t2 = Expr1.typ_of_expr e2' in
      if t1 = `Int || t1 = `Real || t2 = `Int || t2 = `Real
      then (* more precision by turning x = y into x >= y && y >= x *)
        let e1' = Expr1.Apron.of_expr e1' in
        let e2' = Expr1.Apron.of_expr e2' in
        Expr1.Bool.dand cond
          (Expr1.Apron.supeq cond (Expr1.Apron.sub cond e1' e2'))
          (Expr1.Apron.supeq cond (Expr1.Apron.sub cond e2' e1'))
        |> Expr1.Bool.to_expr
      else Expr1.Bool.to_expr (Expr1.eq cond e1' e2')
  | And (e1, e2) -> make_bool_expr env cond Expr1.Bool.dand e1 e2
  | Or (e1, e2) -> make_bool_expr env cond Expr1.Bool.dor e1 e2
  | Not e ->
      Expr1.Bool.to_expr (Expr1.Bool.dnot cond (Expr1.Bool.of_expr (make_expr1 env cond e)))
  | True -> Expr1.Bool.to_expr (Expr1.Bool.dtrue env cond)
  | False -> Expr1.Bool.to_expr (Expr1.Bool.dfalse env cond)
  | Cond (e1, e2, e3) ->
      let e1' = Expr1.Bool.of_expr (make_expr1 env cond e1) in
      let e2' = make_expr1 env cond e2 in
      let e3' = make_expr1 env cond e3 in
      Expr1.ite cond e1' e2' e3'
  | _ -> raise Unexpected_expression;;
  
let rec interpret man env cond ctx = function
  | Assign (Ident v, e) ->
      Domain1.assign_lexpr man cond ctx [v] [make_expr1 env cond e] None
  | Seq (e::es) ->
      let ctx' = interpret man env cond ctx e in
      interpret man env cond ctx' (Seq es)
  | Seq [] -> ctx
  | Cond (e1, e2, e3) ->
      let e1' = Expr1.Bool.of_expr (make_expr1 env cond e1) in
      if Expr1.Bool.is_true cond e1'
      then interpret man env cond ctx e2
      else if Expr1.Bool.is_false cond e1'
      then interpret man env cond ctx e3
      else
        let cond' = Cond.copy cond in
        let ctx' = Domain1.meet_condition man cond' ctx e1' in
        let ctx1 = interpret man env cond ctx' e2 in
        let ctx2 = interpret man env cond ctx e3 in
        Domain1.join man ctx1 ctx2
  | _ -> raise Unexpected_expression;;
     
let initialize ds invs =
  let rec generate pairs constraints = function
    | [] -> (pairs, constraints)
    | (Nat_decl str)::ds -> generate ((str, `Int)::pairs) (Ge (Ident str, Nat 0)::constraints) ds
    | (Int_decl str)::ds -> generate ((str, `Int)::pairs) constraints ds
    | (Real_decl str)::ds -> generate ((str, `Real)::pairs) constraints ds
    | (Bool_decl str)::ds -> generate ((str, `Bool)::pairs) constraints ds in
  let (pairs, constraints) = generate [] [] ds in
  let cudd = Cudd.Man.make_v () in (* in the future, may need to change cudd settings *)
  let env = Env.add_vars (Env.make Env.string_symbol cudd) pairs in
  let cond = Cond.make Env.string_symbol cudd in
  let apron = Polka.manager_alloc_loose() in
  let man = Domain1.man_of_mtbdd (Domain1.make_mtbdd apron) in
  let abs = Domain1.top man env in
  let constraints = List.map (fun x -> Expr1.Bool.of_expr (make_expr1 env cond x)) (constraints @ invs) in
  (man, env, cond, List.fold_left (Domain1.meet_condition man cond) abs constraints);;

let interpret_program p =
  let (man, env, cond, ctx) = initialize p.decls p.invs in
  let res = interpret man env cond ctx p.expr in
  printf "res:%a@." (Domain1.print man) res;;
   
(*
let _ =
  let test_prog =
    { decls = [Nat_decl "x"; Int_decl "y"; Bool_decl "b"];
      invs  = [];
      expr  = Seq [Cond (Eq (Ident "x", Nat 0), Assign(Ident "y", Ident "x"), Assign(Ident "y", Nat 0))] } in
  interpret_program test_prog;;*)
