open Ast.Sal_ast;;
open Types;;
open Utils;;

open Apron;;
open Mpqf;;
open Format;;

exception Unimplemented of string;;

(* convert sal_expr into texpr string for parsing *)
let rec arith_to_str se =
  match se with
  | Ident s -> Some s
  | Decimal i -> Some (string_of_int i)
  | Float f -> Some (string_of_float f)
  | Add (e1, e2) -> 
      (match (arith_to_str e1, arith_to_str e2) with
        | (Some e1, Some e2) -> Some ("("^e1^"+"^e2^")")
        | _ -> None)
  | Sub (e1, e2) -> 
      (match (arith_to_str e1, arith_to_str e2) with
        | (Some e1, Some e2) -> Some ("("^e1^"-"^e2^")")
        | _ -> None)
  | Mul (e1, e2) -> 
      (match (arith_to_str e1, arith_to_str e2) with
        | (Some e1, Some e2) -> Some ("("^e1^"*"^e2^")")
        | _ -> None)
  | Div (e1, e2) -> 
      (match (arith_to_str e1, arith_to_str e2) with
        | (Some e1, Some e2) -> Some ("("^e1^"/"^e2^")")
        | _ -> None)
  | _ -> None;;

let rec cond_to_str se =
  match se with
  | Ge (e1, e2) -> 
      (match (arith_to_str e1, arith_to_str e2) with
        | (Some e1, Some e2) -> Some (e1^">="^e2)
        | _ -> None)
  | Gt (e1, e2) -> 
      (match (arith_to_str e1, arith_to_str e2) with
        | (Some e1, Some e2) -> Some (e1^">"^e2)
        | _ -> None)
  | Le (e1, e2) -> 
      (match (arith_to_str e1, arith_to_str e2) with
        | (Some e1, Some e2) -> Some (e1^"<="^e2)
        | _ -> None)
  | Lt (e1, e2) -> 
      (match (arith_to_str e1, arith_to_str e2) with
        | (Some e1, Some e2) -> Some (e1^"<"^e2)
        | _ -> None)
  | Eq (e1, e2) -> 
      (match (arith_to_str e1, arith_to_str e2) with
        | (Some e1, Some e2) -> Some (e1^"="^e2)
        | _ -> None)
  | Neq (e1, e2) ->
      (match (arith_to_str e1, arith_to_str e2) with
        | (Some e1, Some e2) -> Some (e1^"!="^e2)
        | _ -> None)
  | _ -> None;;

(* get a def as a string *)
let def_to_string ad =
  match ad with
  | Nat v -> "Nat " ^ v
  | Int v -> "Int " ^ v
  | Real v -> "Real " ^ v
  | Bool v -> "Bool " ^ v
  | _ -> "Other"

(* get def from a sal_type and variable name; only Base_types handled right now *)
let rec get_def st v =
  match st with
    | Base_type("NATURAL") -> Some (Nat v)
    | Base_type("INTEGER") -> Some (Int v)
    | Base_type("REAL") -> Some (Real v)
    | Base_type("BOOL") -> Some (Bool v)
    | Base_type(other) -> printf "other base type: %s " other; None
    | _ -> None;;

(* convert a sal_def to a def *)
let sal_to_def sd =
  match sd with
    | Type_def (v, st) -> get_def st v
    | Constant_decl (v, st) ->
        (match (get_def st v) with
        | Some d -> Some (Const d)
        | _ -> None)
    | Constant_def (v, st, se) ->
        (match (get_def st v, arith_to_str se) with
        | (Some d, Some e) -> Some (Const_val (d, v ^ "=" ^ e))
        | _ -> None)
    | _ -> None;;

(* convert a sal_assignment list (only Assign assignments) to a pair of an abstract variable and
   a list of variables' names that have been assigned to *)
let get_assigns assigns man env =
  let rec to_str_list a assign_strs assigned =
    match a with
      | [] -> (assign_strs, assigned)
      | (Assign (Ident v, e))::ls -> printf "ident = %s, " v;
          (match arith_to_str e with
          | Some expr -> printf "expr = %s, " expr; to_str_list ls ((v ^ "=" ^ expr)::assign_strs) (v::assigned)
          | None -> to_str_list ls assign_strs (v::assigned))
      | _::ls -> to_str_list ls assign_strs assigned in
  let (assign_strs, assigned) = to_str_list assigns [] [] in
  (Abstract1.of_tcons_array man env (Parser.tcons1_of_lstring env (assign_strs)), assigned);;

(* generate an abstract variable capturing a variable retaining its value in the next-state *)
let get_unchanged next_names man env =
  let gen_assign v = v ^ "=" ^ (String.sub v 0 (String.length v - 1)) in
  Abstract1.of_lincons_array man env (Parser.lincons1_of_lstring env (List.map gen_assign next_names));;

(* capture explicit and implicit assignments for all next-state variables in an abstract variable *)
let get_full_assigns assigns next_vars man env =
  let listdiff ls1 ls2 = List.filter (fun x -> not (List.mem x ls2)) ls1 in
  let (explicit, assigned) = get_assigns assigns man env in
  let implicit = get_unchanged (listdiff next_vars assigned) man env in
  printf "full: %a@." Abstract1.print (Abstract1.meet man explicit implicit);
  Abstract1.meet man explicit implicit;;

(* convert a conditional sal_expr to a cond *)
let get_conds cond man env =
  let rec to_str_list c =
    match c with
      | And (e1, e2) -> Abstract1.meet man (to_str_list e1) (to_str_list e2)
      | Or (e1, e2) -> Abstract1.join man (to_str_list e1) (to_str_list e2)
      | True -> Abstract1.top man env
      | False -> Abstract1.bottom man env
      | _ ->
        (match cond_to_str c with
          | Some expr -> Abstract1.of_tcons_array man env (Parser.tcons1_of_lstring env [expr])
          | None -> Abstract1.top man env) in
  to_str_list cond

let get_guardeds gls (next_vars: string list) man env invs =
  let rec to_guardeds gcs res =
    match gcs with
    | (ExistentialGuarded (decl, gc))::gcs -> to_guardeds (gc::gcs) res
    | (Guarded (cond, assigns))::gcs ->
      let assigns_abs = Abstract1.meet man invs (get_full_assigns assigns next_vars man env) in
      let cond_abs = get_conds cond man env in
      to_guardeds gcs ({ guard = cond_abs; expr = assigns_abs }::res)
    | [Default assigns] -> (res, Abstract1.meet man invs (get_full_assigns assigns next_vars man env))
    | [] -> to_guardeds [Default []] res
    | _ -> raise (Unimplemented "Default not at end.") in
  to_guardeds gls [];;
  


(*
  let is_def gc = match gc with Default _ -> true | _ -> false in
  let rec sal_to_apron_guarded gc =
    match gc with
    | ExistentialGuarded (decl, gc2) -> sal_to_apron_guarded gc2 (* ignore quantifier *)
    | Guarded (expr, assigns) ->
        let assigns_abs = Abstract1.meet man invs (get_full_assigns assigns next_vars man env) in
          printf "assigns_abs: %a@." Abstract1.print assigns_abs;
        let expr_abs = get_conds expr man env in
          printf "conds: %a@." Abstract1.print expr_abs;
          printf "meet: %a@." Abstract1.print (Abstract1.meet man assigns_abs expr_abs);
          Abstract1.meet_array man [|invs; assigns_abs; expr_abs|]
    | Default assigns -> Abstract1.meet man invs (get_full_assigns assigns next_vars man env) in
  let ls = List.map sal_to_apron_guarded gls in
  let ls' = if (List.fold_left (||) false (List.map is_def gls)) then ls else ls@[get_unchanged [] man env] in
    List.map (printf "to join: %a@." Abstract1.print) ls';
    let joined = Abstract1.join_array man (Array.of_list ls') in
    printf "joined all: %a@." Abstract1.print joined;
    printf "meet invs: %a@." Abstract1.print (Abstract1.meet man invs joined);
  Abstract1.join_array man (Array.of_list (List.map sal_to_apron_guarded gls));;
*)

(* get state_vars from a list of defs *)
let get_state_vars ds =
  let rec get_svs vs (svs : state_vars) =
    match vs with
    | [] -> svs 
    | (Some (Nat v))::vs ->
        get_svs vs
          ({ svs with
              current_ints = (Var.of_string v)::svs.current_ints
            ; next_ints    = (Var.of_string (v^"'"))::svs.next_ints
            ; constraints  = (v^">=0")::(v^"'>=0")::svs.constraints })
    | (Some (Int v))::vs ->
        get_svs vs
          { svs with
              current_ints = (Var.of_string v)::svs.current_ints
            ; next_ints    = (Var.of_string (v^"'"))::svs.next_ints }
    | (Some (Real v))::vs ->
        get_svs vs
          { svs with
              current_reals = (Var.of_string v)::svs.current_reals
            ; next_reals    = (Var.of_string (v^"'"))::svs.next_reals }
    | (Some (Const_val (Nat v, expr)))::vs ->
        get_svs vs
          { svs with
              constant_ints = (Var.of_string v)::svs.constant_ints
            ; constraints   = (v^">=0")::expr::svs.constraints }
    | (Some (Const_val (Int v, expr)))::vs ->
        get_svs vs
          { svs with
              constant_ints = (Var.of_string v)::svs.constant_ints
            ; constraints   = expr::svs.constraints }
    | (Some (Const_val (Real v, expr)))::vs ->
        get_svs vs
          { svs with
              constant_reals = (Var.of_string v)::svs.constant_ints
            ; constraints    = expr::svs.constraints }
    | (Some (Const (Nat v)))::vs ->
        get_svs vs
          { svs with
              constant_ints = (Var.of_string v)::svs.constant_ints
            ; constraints   = (v^">=0")::svs.constraints }
    | (Some (Const (Int v)))::vs ->
        get_svs vs { svs with constant_ints = (Var.of_string v)::svs.constant_ints }
    | (Some (Const (Real v)))::vs ->
        get_svs vs { svs with constant_reals = (Var.of_string v)::svs.constant_ints }
    | _::vs -> get_svs vs svs in
  get_svs ds
    { current_ints = []
    ; next_ints = []
    ; constant_ints = []
    ; current_reals = []
    ; next_reals = []
    ; constant_reals = []
    ; constraints = []};;

(* get state_vars from a list of sal_decls *)
let sal_decls_to_state_vars sds =
  let make_vars (names, st) = List.map (get_def st) names in
  get_state_vars (List.flatten (List.map make_vars sds));;

(* convert a string and sal_module to a trans_sys *)
let sal_to_apron_module str sal_mod man ctx_vars =
  let vars = sal_decls_to_state_vars (List.flatten (List.map snd (sal_mod.state_vars))) in
  let env = List.map (fun x -> printf "%s " (Var.to_string x)) (vars.current_ints @ vars.next_ints @ vars.current_reals @ vars.next_reals);
            Environment.make
              (Array.of_list (vars.current_ints @ vars.next_ints @ vars.constant_ints @ ctx_vars.constant_ints))
              (Array.of_list (vars.current_reals @ vars.next_reals @ vars.constant_reals @ ctx_vars.constant_reals)) in
  let invs = Abstract1.of_tcons_array man env (Parser.tcons1_of_lstring env (ctx_vars.constraints @ vars.constraints)) in
  let init = printf "%s " "init "; Abstract1.meet man invs (fst (get_assigns (sal_mod.initialization) man env)) in
  let trans =
    let next_names = List.map Var.to_string (vars.next_ints @ vars.next_reals) in
    match sal_mod.transition with
    | NoTransition -> Assignment (get_unchanged next_names man env)
    | Assignments als -> Assignment (fst (get_assigns als man env))
    | GuardedCommands gls -> Guarded (get_guardeds gls next_names man env invs) in
  { man; vars; env; invs; init; trans };;

(* process sal_def list into apron_defs and apron_modules *)
let handle_sal_defs sal_defs man =
  printf "%s " "handle"; let rec handler defs (ads, ams) =
    match defs with
      | [] -> (ads, ams)
      | ((Module_def (str, sal_mod))::ds) ->
          let vars = get_state_vars ads in
          let am = sal_to_apron_module str sal_mod man vars in
            handler ds (ads, am::ams)
      | (d::ds) -> handler ds ((sal_to_def d)::ads, ams) (* not handled right now *) in
  let (ads, ams) = handler sal_defs ([],[]) in
    List.map print_trans_sys ams; ams;;
