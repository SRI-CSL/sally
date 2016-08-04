(* Interpret simple programs *)
open Simple_ast;;
open Bddapron;;
open Bddapron.Syntax;;
open Apron;;
open Format;;

exception Unimplemented of string;;
exception Unexpected_expression;;

(* Make a boolean expression out of two boolean expressions
   e1 and e2 and a boolean binary operator binop *)
let rec make_bool_expr env cond binop e1 e2 =
  let e1' = Expr1.Bool.of_expr (make_expr1 env cond e1) in
  let e2' = Expr1.Bool.of_expr (make_expr1 env cond e2) in
  Expr1.Bool.to_expr (binop cond e1' e2')

and

(* Make a comparison relative to zero, e.g. e > 0 *)
make_apron_comp env cond cmp e =
  let e' = Expr1.Apron.of_expr (make_expr1 env cond e) in
  Expr1.Bool.to_expr (cmp cond e')

and

(* Make Expr1.ts for the RHS of an assignment or condition in a conditional statement *)
make_expr1 env cond = function
  | Nat e -> make_expr1 env cond (Int e)
  | Int e -> Expr1.Apron.to_expr (Expr1.Apron.cst env cond (Coeff.Scalar (Scalar.of_int e)))
  | Float e -> Expr1.Apron.to_expr (Expr1.Apron.cst env cond (Coeff.Scalar (Scalar.of_float e)))
  | Ident e -> Expr1.var env cond e
  (* Arithmetic operators (i.e., And, Sub, Mul, Div) currently use default type (e.g. REAL, INT) and
     rounding settings *)
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
  
(* Interpret a simple program consisting of sequences of assignments and conditionals (containing assignments) *)
let rec interpret carry_conditionals man env cond inv ctx = function
  | Assign (Ident v, Constrained f) ->
      let ctx' = Domain1.forget_list man ctx [v] in
      Domain1.meet man ctx' (interpret carry_conditionals man env cond inv ctx (f (Ident v)))
      (* Domain1.meet_condition man cond ctx (Expr1.Bool.of_expr (make_expr1 env cond (f (Ident v)))) *)
      |> Domain1.meet man inv
  | Assign (Ident v, e) ->
      Domain1.assign_lexpr man cond ctx [v] [make_expr1 env cond e] None
      |> Domain1.meet man inv
  | Seq (e::es) ->
      let ctx' = interpret carry_conditionals man env cond inv ctx e in
      interpret carry_conditionals man env cond inv ctx' (Seq es)
  | Seq [] -> ctx
  | Cond (e1, e2, e3) ->
      let e1' = Expr1.Bool.of_expr (make_expr1 env cond e1)
                |> Domain1.meet_condition man cond ctx in
      if Domain1.is_eq man ctx e1' (* adding condition e1 does not reduce the domain *)
      then interpret carry_conditionals man env cond inv ctx e2
      else if Domain1.is_bottom man e1' (* condition e1 cannot hold in ctx *)
      then interpret carry_conditionals man env cond inv ctx e3
      else
        (* cannot tell if e1 holds or not, so take both branches, assuming e1 holds in the
           first branch and that it does not in the second *)
        let e1' = if carry_conditionals then e1' else ctx in
        let ctx1 = interpret carry_conditionals man env cond inv e1' e2 in
        let not_e1' = Expr1.Bool.of_expr (make_expr1 env cond (Not e1))
                      |> Domain1.meet_condition man cond ctx in
        let not_e1' = if carry_conditionals then not_e1' else ctx in
        let ctx2 = interpret carry_conditionals man env cond inv not_e1' e3 in
        Domain1.join man ctx1 ctx2 |> Domain1.meet man inv
  | Local (e1, e2) ->
      let rec add_to_env env inv = function
        | Nat_decl str -> 
            let env' = Env.add_vars env [(str, `Int)] in
            let inv = Domain1.change_environment man inv env' in
            let inv' = Domain1.meet_condition man cond inv (Expr1.Bool.of_expr (make_expr1 env' cond (Ge (Ident str, Nat 0)))) in
            (env', inv', str)
        | Int_decl str -> 
            let env' = Env.add_vars env [(str, `Int)] in
            let inv = Domain1.change_environment man inv env' in
            (env', inv, str)
        | Real_decl str ->
            let env' = Env.add_vars env [(str, `Real)] in
            let inv = Domain1.change_environment man inv env' in
            (env', inv, str)
        | Bool_decl str ->
            let env' = Env.add_vars env [(str, `Bool)] in
            let inv = Domain1.change_environment man inv env' in
            (env', inv, str)
        | Enum_def (str, strs) ->
            let env' = Env.add_typ env str (`Benum (Array.of_list strs)) in
            let inv = Domain1.change_environment man inv env' in
            (env', inv, str)
        | Enum_decl (str, enum) ->
            let env' = Env.add_vars env [(str, `Benum enum)] in
            let inv = Domain1.change_environment man inv env' in
            (env', inv, str)
        | Constraint_decl (decl, constr) ->
            let (env', inv, str) = add_to_env env inv decl in
            let inv = Domain1.change_environment man inv env' in
            (env', Domain1.meet_condition man cond inv (Expr1.Bool.of_expr (make_expr1 env' cond constr)), str) in
      let (env', inv', str) = add_to_env env inv e1 in
      let ctx' = Domain1.change_environment man ctx env' |> Domain1.meet man inv' in
      let res = interpret carry_conditionals man env' cond inv' ctx' e2 in
      Domain1.change_environment man res env
  | other -> Domain1.meet_condition man cond inv (Expr1.Bool.of_expr (make_expr1 env cond other));;
     
let initialize apron ds invs =
  let rec generate pairs constraints env = function
    | [] -> (pairs, constraints, env)
    | (Nat_decl str)::ds -> generate ((str, `Int)::pairs) (Ge (Ident str, Nat 0)::constraints) env ds
    | (Int_decl str)::ds -> generate ((str, `Int)::pairs) constraints env ds
    | (Real_decl str)::ds -> generate ((str, `Real)::pairs) constraints env ds
    | (Bool_decl str)::ds -> generate ((str, `Bool)::pairs) constraints env ds
    | (Enum_def (str, strs))::ds -> generate pairs constraints (Env.add_typ env str (`Benum (Array.of_list strs))) ds
    | (Enum_decl (str, enum))::ds -> generate ((str, `Benum enum)::pairs) constraints env ds
    | (Constraint_decl (decl, cond))::ds -> generate pairs (cond::constraints) env (decl::ds) in
  let cudd = Cudd.Man.make_v () in (* in the future, may need to make cudd parameterizable *)
  Cudd.Man.set_gc 10000
    (begin fun () -> printf "@.CUDD GC@." end)
    (begin fun () -> printf "@.CUDD REORDER@." end);
  let (pairs, constraints, env) = generate [] [] (Env.make ~symbol:Env.string_symbol ~bddsize:(10 + List.length ds) cudd) ds in
  let env = Env.add_vars env pairs in (* create an environment with declared variables *)
  let cond = Cond.make Env.string_symbol cudd in
  let man = Domain1.man_of_mtbdd (Domain1.make_mtbdd apron) in (* to do: make this a parameter *)
  let abs = Domain1.top man env in
  let constraints = List.map (fun x -> Expr1.Bool.of_expr (make_expr1 env cond x)) (constraints @ invs) in
  (man, env, cond, List.fold_left (Domain1.meet_condition man cond) abs constraints);;

let interpret_program carry_conditionals apron_man p =
  let (man, env, cond, ctx) = initialize apron_man p.decls p.invs in
  let res = interpret carry_conditionals man env cond ctx ctx p.expr in
  printf "result:%a@." (Domain1.print man) res;;
   
(*
let _ =
  let test_prog =
    { decls = [Nat_decl "x"; Nat_decl "y"; Bool_decl "b"];
      invs  = [];
      expr  = Seq []} in
  let (man, env, cond, ctx) = initialize (Box.manager_alloc()) (test_prog.decls) [] in
  let ctx1 = make_expr1 env cond (Eq (Ident "x", Nat 1)) |> Expr1.Bool.of_expr |> Domain1.meet_condition man cond ctx in
  let ctx2 = make_expr1 env cond (Eq (Ident "x", Nat 2)) |> Expr1.Bool.of_expr |> Domain1.meet_condition man cond ctx in
  let ctx3 = make_expr1 env cond (Eq (Ident "x", Nat 3)) |> Expr1.Bool.of_expr |> Domain1.meet_condition man cond ctx in
  let ctx4 = make_expr1 env cond (Gt (Nat 10, Add (Ident "x", Ident "y"))) |> Expr1.Bool.of_expr |> Domain1.meet_condition man cond ctx in
  let ctx1234 = Domain1.join man ctx1 ctx2 |> Domain1.join man ctx3 |> Domain1.join man ctx3 in
  printf "join 1234: %a@." (Domain1.print man) ctx1234;
  let ctx1243 = Domain1.join man ctx1 ctx2 |> Domain1.join man ctx4 |> Domain1.join man ctx4 in
  printf "join 1243: %a@." (Domain1.print man) ctx1243;;*)
