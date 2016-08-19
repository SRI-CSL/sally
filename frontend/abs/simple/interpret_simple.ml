(** Interpret simple programs *)
open Simple_ast;;
open Print_simple;;
open Bddapron;;
open Bddapron.Syntax;;
open Apron;;
open Format;;

exception Unimplemented of string;;
exception Unexpected_expression;;

(** [make_bool_expr env cond binop e1 e2] makes a boolean expression out of two
    boolean expressions [e1] and [e2] and a boolean binary operator [binop] *)
let rec make_bool_expr env cond binop e1 e2 =
  let e1' = Expr1.Bool.of_expr (make_expr1 env cond e1) in
  let e2' = Expr1.Bool.of_expr (make_expr1 env cond e2) in
  Expr1.Bool.to_expr (binop cond e1' e2')

and

(** [make_apron_comp env cond cmp e] makes a comparison (determined by [cmp])
    relative to zero, e.g. [e > 0] *)
make_apron_comp env cond cmp e =
  let e' = Expr1.Apron.of_expr (make_expr1 env cond e) in
  Expr1.Bool.to_expr (cmp cond e')

and

(** Make [Expr1.t]s for the RHS of an assignment or condition in a conditional statement *)
make_expr1 env cond = function
  | Nat e -> make_expr1 env cond (Int e)
  | Int e -> Expr1.Apron.to_expr (Expr1.Apron.cst env cond (Coeff.Scalar (Scalar.of_int e)))
  (* TODO: Where are reals? *)
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
      (* TODO: Make sure that Real doesn't mean Float *)
      (** = replaced with <= and >= *)
      (match t1, t2 with
        | (`Int | `Real), (`Int | `Real) ->
          let e1' = Expr1.Apron.of_expr e1' in
          let e2' = Expr1.Apron.of_expr e2' in
            Expr1.Bool.dand cond
              (Expr1.Apron.supeq cond (Expr1.Apron.sub cond e1' e2'))
              (Expr1.Apron.supeq cond (Expr1.Apron.sub cond e2' e1'))
            |> Expr1.Bool.to_expr
        | _ -> Expr1.Bool.to_expr (Expr1.eq cond e1' e2')
      )
  | And (e1, e2) ->
      make_bool_expr env cond Expr1.Bool.dand e1 e2
  | Or (e1, e2) ->
      make_bool_expr env cond Expr1.Bool.dor e1 e2
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

(** Interpret a simple program:
    [interpret carry_conditionals man env cond inv ctx prog]
    interprets program [prog] in the context [ctx] with invariants
    [inv]. *)
let rec interpret man env cond inv ctx = function
  | Assign (Ident v, Constrained f) ->
      let ctx' = Domain1.forget_list man ctx [v] in
      Domain1.meet man ctx' (interpret man env cond inv ctx (f (Ident v)))
      (* Domain1.meet_condition man cond ctx (Expr1.Bool.of_expr (make_expr1 env cond (f (Ident v)))) *)
      |> Domain1.meet man inv
  | Assign (Ident v, e) ->
      Domain1.assign_lexpr man cond ctx [v] [make_expr1 env cond e] None
      |> Domain1.meet man inv
  | Seq (e::es) ->
      let ctx' = interpret man env cond inv ctx e in
      interpret man env cond inv ctx' (Seq es)
  | Seq [] -> printf "%a@." (Domain1.print man) ctx; ctx
  | Branch es ->
      let ctx's = List.map (interpret man env (Cond.copy cond) inv ctx) es in
      let res = List.fold_left (Domain1.join man) (Domain1.bottom man env) ctx's in
      res
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
      let res = interpret man env' cond inv' ctx' e2 in
      Domain1.change_environment man res env
  | other ->
(* let condition' = of_apron man env (Abstract1.meet (Abstract1.top env.Env.eapron) condition in*)
     let condition = Expr1.Bool.of_expr (make_expr1 env cond other) in
     let condition' = Domain1.meet_condition man cond ctx condition in
(*
     let apron_man = Domain1.man_get_apron man in
     let apron_env = env.Bdd.Env.ext.Bddapron.Env.eapron in
     let apron_cond = List.fold_left (Apron.Abstract1.join apron_man) (Abstract1.bottom apron_man apron_env) (List.map snd (Domain1.to_bddapron man condition')) in
     let condition' = Domain1.of_apron man env apron_cond in condition';*)
(*     let condition' = Domain1.meet_condition man (Cond.copy cond) ctx condition in *)
     Domain1.meet man inv condition';;

(** Initialize a domain:
      [initialize apron ds invs cond_size]
    creates an environment containing all declarations in the list [ds],
    a bddapron manager [man] based off of the apron manager [apron],
    a conditional BDD of size [cond_size], and
    invariants in [invs] and arising from type declarations *)
let initialize apron ds invs cond_size =
 let rec manage_decl ((pairs, constraints, env) as acc) = function
    | Nat_decl str -> (str, `Int)::pairs, Ge (Ident str, Nat 0)::constraints, env
    | Int_decl str -> (str, `Int)::pairs, constraints, env
    | Real_decl str -> (str, `Real)::pairs, constraints, env
    | Bool_decl str -> (str, `Bool)::pairs, constraints, env
    | Enum_def (str, strs) -> pairs, constraints, Env.add_typ env str (`Benum (Array.of_list strs))
    | Enum_decl (str, enum) -> (str, `Benum enum)::pairs, constraints, env
    | Constraint_decl (decl, cond) -> let pairs, constraints, env = manage_decl acc decl in
                                      pairs, cond::constraints, env
  in
  let generate = List.fold_left manage_decl in
  let cudd = Cudd.Man.make_v () in (* in the future, may need to make cudd more parameterizable *)
  Cudd.Man.set_gc 1000000
    (begin fun () -> Cudd.Man.print_info cudd; printf "@.CUDD GC@." end)
    (begin fun () -> printf "@.CUDD REORDER@." end);
  let (pairs, constraints, env) = generate ([], [], (Env.make ~symbol:Env.string_symbol ~bddsize:(100) cudd)) ds in
  let env = Env.add_vars env pairs in (* create an environment with declared variables *)
  let cond = Cond.make ~symbol:Env.string_symbol ~bddsize:(cond_size) cudd in
  let man = Domain1.man_of_bdd (Domain1.make_bdd apron) in
  let abs = Domain1.top man env in
  printf "%s@." "constraints";
  let constraints = List.map (fun x -> (interpret man env cond abs abs x)) (constraints @ invs) in
  (man, env, cond, List.fold_left (Domain1.meet man) abs constraints);;

let interpret_program apron_man p cond_size =
  let (man, env, cond, ctx) = initialize apron_man p.decls p.invs cond_size in
  let res = interpret man env cond ctx ctx p.expr in
  printf "result:%a@." (Domain1.print man) res;;
