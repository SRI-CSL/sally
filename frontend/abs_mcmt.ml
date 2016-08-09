open Abs.Mcmt_lexer;;
open Abs.Mcmt_to_simple_ast;;
open Abs.Print_simple;;
open Abs.Mcmt_simple_ast;;
open Abs.Interpret_simple;;
open Abs;;
open Bddapron;;
open Format;;

exception Malformed_mcmt_prog;;

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
(*
  printf "index: %d@." (env.Bdd.Env.bddindex0);
  printf "env: %a@." (Env.print) env;;*)
  if (Domain1.is_eq man ctx ctx')
  then ctx
  else if cnt = 0 then
    let widened = Domain1.widening man ctx ctx' in
    let narrowed = eval_step man env inv cond ts (interpret true man env cond inv widened ts.trans) |> Domain1.join man ctx in
    eval_mcmt man env cond inv narrowed ts lim lim
  else eval_mcmt man env cond inv ctx' ts lim (cnt - 1);;

let eval_mcmt_prog ts =
  let decls = ts.decls @ ts.current_sv_decls @ ts.next_sv_decls in
  let invs = ts.invs in
  let (man, env, cond, ctx) = initialize (Polka.manager_alloc_strict()) decls invs in
  let init = interpret true man env cond ctx ctx ts.init in
  printf "initial state: %a@." (Domain1.print man) init;
  let res = eval_mcmt man env cond ctx init ts 5 5 in
  printf "res: %a@." (Domain1.print man) res;;

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
