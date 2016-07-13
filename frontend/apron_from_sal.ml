open Ast.Sal_ast;;

open Apron;;
open Mpqf;;
open Format;;

exception Unimplemented of string;;

let manbox = Box.manager_alloc ();;
let manpk = Polka.manager_alloc_strict ();;

(* convert arithmetic sal_expr into texpr string for parsing *)
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

(* convert conditional sal_expr into texpr string for parsing *)
let cond_to_str se =
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
  | _ -> None

(* capture an apron variable's sal_type, including different sal Base_types; ignore Subtype, IntegerRange/Proc for now *)
type def =
  | Nat of string
  | Int of string
  | Real of string
  | Bool of string
  | Bounded of string * string * string (* Range, Enum *)
  | Arr of string * def * def
  | Const of def * string;;

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
    | _ -> None;;

(* convert a sal_def to an def *)
let sal_to_apron_def sd =
  match sd with
    | Type_def (v, st) -> get_def st v
    | Constant_decl (v, st) -> get_def st v
    | Constant_def (v, st, se) ->
        match (get_def st v, arith_to_str se) with
        | (Some d, Some e) -> Some (Const (d, v ^ "=" ^ e))
        | _ -> None
    | _ -> None;;

(* convert a sal_assignment list (only Assign assignments) to a pair of an abstract variable and
   a list of variables' names that have been assigned to *)
let get_assigns assigns man env =
  let rec to_str_list a assign_strs assigned =
    match a with
      | [] -> (assign_strs, assigned)
      | (Assign (Ident v, e))::ls ->
          (match arith_to_str e with
          | Some expr -> to_str_list ls ((v ^ "=" ^ expr)::assign_strs) (v::assigned)
          | None -> to_str_list ls assign_strs assigned)
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
  Abstract1.meet man explicit implicit;;

(* convert a conditional sal_expr to an abstract variable *)
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

let get_guardeds gls (next_vars: string list) man env =
  let rec sal_to_apron_guarded gc =
    match gc with
      | ExistentialGuarded (decl, gc2) -> sal_to_apron_guarded gc2 (* ignore quantifier *)
      | Guarded (expr, assigns) ->
          let assigns_abs = get_full_assigns assigns next_vars man env in
          let expr_abs = get_conds expr man env in
          let abs = Abstract1.meet man assigns_abs expr_abs in
          printf "tr=%a@." Abstract1.print assigns_abs;
          printf "cond=%a@." Abstract1.print expr_abs;
          printf "abs=%a@." Abstract1.print abs;
          abs
      | Default assigns -> get_full_assigns assigns next_vars man env in
  Abstract1.join_array man (Array.of_list (List.map sal_to_apron_guarded gls))

type state_vars =
  { current_ints  : Var.t list
  ; next_ints     : Var.t list
  ; current_reals : Var.t list
  ; next_reals    : Var.t list
  ; constraints   : string list }

(* get state_vars from a list of sal_decls *)
let get_state_vars sds =
  let make_vars (names, st) =
    List.map (get_def st) names in
  let rec get_svs vs { current_ints; next_ints; current_reals; next_reals; constraints } =
    match vs with
    | [] -> { current_ints; next_ints; current_reals; next_reals; constraints }
    | (Some (Nat v))::vs ->
        get_svs vs
          { current_ints = (Var.of_string v)::current_ints
          ; next_ints = (Var.of_string (v^"'"))::next_ints
          ; current_reals
          ; next_reals
          ; constraints = (v^">=0")::(v^"'>=0")::constraints }
    | (Some (Int v))::vs ->
        get_svs vs
          { current_ints = (Var.of_string v)::current_ints
          ; next_ints = (Var.of_string (v^"'"))::next_ints
          ; current_reals
          ; next_reals
          ; constraints }
    | (Some (Real v))::vs ->
        get_svs vs
          { current_ints
          ; next_ints
          ; current_reals = (Var.of_string v)::current_reals
          ; next_reals = (Var.of_string (v^"'"))::next_reals
          ; constraints }
    | _::vs -> get_svs vs { current_ints; next_ints; current_reals; next_reals; constraints } in
  get_svs (List.flatten (List.map make_vars sds))
          { current_ints = []; next_ints = []; current_reals = []; next_reals = []; constraints = []};;

(* a transition system's Apron components *)
type ('a, 'b) trans_sys =
  { man        : 'b Manager.t
  ; vars       : state_vars
  ; env        : Environment.t
  ; invs       : 'a Abstract1.t
  ; init       : 'a Abstract1.t
  ; transition : 'a Abstract1.t }

let print_trans_sys { vars; env; invs; init; transition } =
  printf "invs=%a@.init=%a@.transition=%a@." Abstract1.print invs Abstract1.print init Abstract1.print transition;;

(* convert a string and sal_module to a trans_sys *)
let sal_to_apron_module str sal_mod man =
  let vars = get_state_vars (List.flatten (List.map snd (sal_mod.state_vars))) in
  let env = Environment.make
              (Array.of_list (vars.current_ints @ vars.next_ints))
              (Array.of_list (vars.current_reals @ vars.next_reals)) in
  let invs = Abstract1.of_tcons_array man env (Parser.tcons1_of_lstring env vars.constraints) in
  let init = fst (get_assigns (sal_mod.initialization) man env) in
  let transition =
    let next_names = List.map Var.to_string (vars.next_ints @ vars.next_reals) in
    match sal_mod.transition with
    | NoTransition -> get_unchanged next_names man env
    | Assignments als -> fst (get_assigns als man env)
    | GuardedCommands gls -> get_guardeds gls next_names man env in
  { man; vars; env; invs; init; transition };;

(* process sal_def list into apron_defs and apron_modules *)
let handle_sal_defs sal_defs man =
  let rec handler defs (ads, ams) =
    match defs with
      | [] -> (ads, ams)
      | ((Module_def (str, sal_mod))::ds) ->
          let am = sal_to_apron_module str sal_mod man in
            handler ds (ads, am::ams)
      | (d::ds) -> handler ds (ads, ams) (* not handled right now *) in
  let (ads, ams) = handler sal_defs ([],[]) in
    List.map print_trans_sys ams; ams;;

(* set current-state values to next-state values and forget next-state constraints *)
let next_abs vars man abs =
  let current = vars.current_ints @ vars.current_reals in
  let next = vars.next_ints @ vars.next_reals in
  let renamed = Abstract1.rename_array man abs (Array.of_list (current @ next)) (Array.of_list (next @ current)) in
  Abstract1.forget_array man renamed (Array.of_list next) false;;

(* one step of the transition relation; stop stepping once fixed point reached *)
let rec step { man; vars; env; invs; init; transition } pred =
  let next = Abstract1.join man pred (next_abs vars man (Abstract1.meet man transition pred)) in
    (*printf "step=%a@." Abstract1.print next;*)
    if Abstract1.is_eq man next pred then next else step { man; vars; env; invs; init; transition } next;;

(* from frontend *)
let create_channel_in = function
  | Some filename -> open_in filename
  | None -> stdin

let create_channel_out = function
  | Some filename -> open_out filename
  | None -> stdout

let _ =
  let mcmt_output = ref None in
  let only_convert = ref false in
  let engine = ref "kind" in
  let rest = ref "" in
  let input_file = ref None in
  let sally_cmd = ref "" in
  (let open Arg in
   Arg.parse [
     "--to-mcmt", String (fun s -> mcmt_output := Some s; only_convert := true), "Only convert input file to mcmt, and exit.";
     "--output-mcmt", Set only_convert, "Only convert input files to mcmt, print the result to stdout or to the file given with -to-mcmt, and exit.";
     "--engine", Set_string engine, "Use the given engine in Sally";
     "--", Rest (fun s -> rest := !rest ^ " " ^ s), "Give these options to Sally";
     "--sally-bin", Set_string sally_cmd, "Sally binary path";
   ] (fun f ->
       input_file := Some f) "Frontend for Sally, use '-- options' to give options to Sally.");
  if !sally_cmd = "" then
    sally_cmd := Find_binary.find "sally" ["./sally"; "src/sally"; "../src/sally"; Sys.executable_name ^ "/../../src/sally"];
  create_channel_in !input_file
  |> Io.Sal_lexer.parse
  |> fun x -> handle_sal_defs x.definitions manpk
  |> List.map (fun ts -> step ts ts.init)
  |> List.map (printf "%a@." Abstract1.print)
