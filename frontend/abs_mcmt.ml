open Abs.Mcmt_lexer;;
open Abs.Mcmt_to_simple_ast;;
open Abs.Print_simple;;
open Abs.Mcmt_simple_ast;;
open Abs.Interpret_simple;;
open Abs;;
open Bddapron;;
open Format;;

exception Malformed_mcmt_prog;;
exception Unexpected_lincons;;
exception Backtrack;;

let eval_step man env inv cond ts ctx =
  let string_from_decl = function
    | Simple_ast.Nat_decl str -> str
    | Simple_ast.Int_decl str -> str
    | Simple_ast.Real_decl str -> str
    | Simple_ast.Bool_decl str -> str
    | Simple_ast.Enum_decl (str, _) -> str
    | _ -> raise Malformed_mcmt_prog in
  let current = List.map string_from_decl ts.current_sv_decls in
  let next = List.map string_from_decl ts.next_sv_decls in
  printf "ctx: %a@." (Domain1.print man) ctx;
  let next_exprs = List.map (Expr1.var env cond) next in
  let assigned = Domain1.assign_lexpr man cond ctx current next_exprs None in
  let forget = Domain1.forget_list man assigned next in
  Domain1.meet man inv forget;;

let rec eval_mcmt man env cond inv ctx ts lim cnt =
  let ctx' = interpret false man env cond inv ctx ts.trans |> eval_step man env inv cond ts |> Domain1.join man ctx in
  printf "ctx': %a@." (Domain1.print man) ctx';
  if (Domain1.is_eq man ctx ctx')
  then ctx
  else if cnt = 0 then
    let widened = Domain1.widening man ctx ctx' in
    let narrowed = eval_step man env inv cond ts (interpret true man env cond inv widened ts.trans) |> Domain1.join man ctx in
    eval_mcmt man env cond inv narrowed ts lim lim
  else eval_mcmt man env cond inv ctx' ts lim (cnt - 1);;

let rec string_of_bdd env ls = function
  | Cudd.Bdd.Bool true -> if ls = [] then "" else "( "^(List.fold_left (fun x y -> x^" "^y) "and" ls)^")"
  | Cudd.Bdd.Bool false -> raise Backtrack
  | Cudd.Bdd.Ite (i, b1, b2) ->
      try string_of_bdd env ((PMappe.find i env.Bdd.Env.idcondvar)::ls) (Cudd.Bdd.inspect b1) with
      _ -> try string_of_bdd env ((PMappe.find i env.Bdd.Env.idcondvar)::ls) (Cudd.Bdd.inspect b2) with
           _ -> raise Backtrack;;

let string_of_lincons env lc =
  let string_of_typ = function
    | Apron.Lincons0.EQ -> "="
    | Apron.Lincons0.SUPEQ -> ">="
    | Apron.Lincons0.SUP -> ">"
    | Apron.Lincons0.DISEQ -> "/="
    | Apron.Lincons0.EQMOD _ -> raise Unexpected_lincons in
  let get_coeff_str = function
    | Apron.Coeff.Scalar s -> Apron.Scalar.to_string s
    | _ -> raise Unexpected_lincons in
  let string_of_term res coeff dim =
    let apron_env = env.Bdd.Env.ext.Bddapron.Env.eapron in
    let coeff_str = get_coeff_str coeff in
    let coeff = float_of_string coeff_str in
    if coeff = 0.0 then ()
    else if coeff = 1.0 then res := (Apron.Environment.var_of_dim apron_env dim |> Apron.Var.to_string)::(!res)
    else res := ("( * "^coeff_str^" "^(Apron.Environment.var_of_dim apron_env dim |> Apron.Var.to_string)^" )")::(!res) in
  let rec sum = function
    | s1::s2::ss -> sum (("( + "^s1^" "^s2^" )")::ss)
    | [s] -> s
    | [] -> "" in
  let string_of_linexpr le =
    let str = ref [] in
    Apron.Linexpr0.iter (string_of_term str) le;
    let res = sum !str in
    let cst = Apron.Linexpr0.get_cst le |> get_coeff_str in
    if (float_of_string cst) = 0.0 then res else "( + "^res^" "^cst^" )" in
  "( "^(string_of_typ lc.Apron.Lincons0.typ)^" "^(string_of_linexpr lc.Apron.Lincons0.linexpr0)^" 0 )";;

let mcmt_of_domain man apron_man env res =
  let res = Domain1.to_bddapron man res in
  let handle_pair (x, y) =
    let bools = Expr1.Bool.to_expr0 x |> Cudd.Bdd.inspect |> string_of_bdd env [] in
    let lincons = (Apron.Abstract1.to_lincons_array apron_man y).Apron.Lincons1.lincons0_array |> Array.map (string_of_lincons env) in
    let abstract =
      if Array.length lincons = 0
      then ""
      else if Array.length lincons = 1
      then Array.get lincons 0
      else "( "^(Array.fold_left (fun x y -> x^" "^y) "and" lincons)^" )" in
   if bools = "" then abstract else "( and "^bools^" "^abstract^" )" in
  let results = List.map handle_pair res in
  "( assume "^
    (if List.length results < 2
    then List.hd results
    else "( "^(List.fold_left (fun x y -> x^" "^y) "or" results)^" )")
  ^" )";;

let eval_mcmt_prog ts =
  let decls = ts.decls @ ts.current_sv_decls @ ts.next_sv_decls in
  let invs = ts.invs in
  let apron_man = Polka.manager_alloc_strict() in
  let (man, env, cond, ctx) = initialize apron_man decls invs in
  let init = interpret true man env cond ctx ctx ts.init in
  printf "initial state: %a@." (Domain1.print man) init;
  let res = eval_mcmt man env cond ctx init ts 5 5 in
  printf "res: %a@." (Domain1.print man) res;
  printf "res: %s@." (mcmt_of_domain man apron_man env res);;
(*
  let res = Domain1.to_bddapron man res in
  List.iter (fun (x, y) -> printf "%s@." (Expr1.Bool.to_expr0 x |> Cudd.Bdd.inspect |> string_of_bdd env []);
             Array.iter (printf "%s@.") ((Apron.Abstract1.to_lincons_array apron_man y).Apron.Lincons1.lincons0_array |> Array.map (string_of_lincons env))) res;;*)

let print_transition_system ts =
  printf "Transition system: %s\n" ts.name;
  List.iter (fun x -> printf "Invariant: %s\n" (string_of_simple x)) ts.invs;
  printf "Initial:%s\n" (string_of_simple ts.init);
  printf "Transition:%s\n" (string_of_simple ts.trans);
  eval_mcmt_prog ts;;

let create_channel_in = function
  | Some filename -> open_in filename
  | None -> stdin;;

let _ =
  let input_file = ref None in
  (let open Arg in
   Arg.parse [] (fun f ->
       input_file := Some f) "");
  create_channel_in !input_file
  |> parse
  |> fun x -> printf "%s\n" "parsed"; mcmt_to_ts x
  |> List.iter print_transition_system;;
