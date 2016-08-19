(** Learn invariants from an mcmt input file *)
open Abs.Mcmt_lexer;;
open Abs.Mcmt_to_simple_ast;;
open Abs.Print_simple;;
open Abs.Mcmt_simple_ast;;
open Abs.Interpret_simple;;
open Abs;;
open Abs.Bddapron_to_mcmt_assumption;;
open Bddapron;;
open Format;;

exception Malformed_mcmt_prog;;
exception Unexpected_lincons;;
exception Backtrack;;

(** Move forward one step in the transition relation *)
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
  let next_exprs = List.map (Expr1.var env cond) next in
  let assigned = Domain1.assign_lexpr man cond ctx current next_exprs None in
  let forget = Domain1.forget_list man assigned next in
  Domain1.meet man inv forget;;

(** Evaluate a transition relation until a fixed point is found:
      [ eval_mcmt man env cond inv ctx ts cnt ]
    will repeatedly apply the transition relation [ts] to the current context [ctx] using
    [man], [env], and [cond];
    move forward one step in the transition relation;
    apply the invariants [inv] to the new domain; and
    decrement [cnt]. When [cnt = 0], widening and narrowing are performed. *)
let rec eval_mcmt man env cond inv init ctx ts cnt =
  let ctx' = interpret false man env cond inv ctx ts.trans |> eval_step man env inv cond ts |>
             (match init with
              | None -> Domain1.join man ctx
              | Some i -> Domain1.join man i) in
  printf "ctx: %a@." (Domain1.print man) ctx;
  printf "ctx': %a@." (Domain1.print man) ctx';
  if (Domain1.is_leq man ctx' ctx)
  then ctx'
  else if cnt = 0 then
    let widened = Domain1.widening man ctx ctx' in
    printf "widened: %a@." (Domain1.print man) widened;
    eval_mcmt man env cond inv init widened ts 0
  else eval_mcmt man env cond inv init ctx' ts (cnt - 1);;

(** Find invariants for a transition system in an mcmt program:
      [ eval_mcmt_prog cond_size iter use_init ts ]
    finds invariants for transition system [ts] by doing abstract interpretation
    for [iter] iterations, where [cond_size] decides
    the initial size for the condition BDD and [use_init] determines whether
    the result from taking one step of the transition is joined with the
    initial state or the previous state. If [cond_size] is too small,
    its size is doubled, and [eval_mcmt_prog] begins again. *)
let rec eval_mcmt_prog cond_size iter use_init ts =
  let decls = ts.decls @ ts.current_sv_decls @ ts.next_sv_decls in
  let invs = ts.invs in
  let apron_man = Polka.manager_alloc_strict() in
  try (
    let (man, env, cond, invariant) = initialize apron_man decls invs cond_size in
    printf "invariant: %a@." (Domain1.print man) invariant;
    let init = interpret true man env cond invariant invariant ts.init in
    printf "initial state: %a@." (Domain1.print man) init;
    let init' = match use_init with true -> Some init | false -> None in
    let res = eval_mcmt man env cond invariant init' init ts iter in
    mcmt_of_domain ts.name man apron_man env res)
  with Bdd.Env.Bddindex -> eval_mcmt_prog (cond_size * 2) iter use_init ts;;

(** [ print_transition_system ts ] prints the transition system [ts]
    after it has been converted into simple ASTs *)
let print_transition_system ts =
  printf "Transition system: %s\n" ts.name;
  List.iter (fun x -> printf "Invariant: %s\n" (string_of_simple x)) ts.invs;
  printf "Initial:%s\n" (string_of_simple ts.init);
  printf "Transition:%s\n" (string_of_simple ts.trans);;

let () =
  let input_file = ref None in
  let num_iterations = ref 10 in
  let use_init = ref true in
  (let open Arg in
   Arg.parse [
     "--iterations", Int (fun x -> num_iterations := x), "Number of iterations for the interpreter";
     "--use-nonstandard-transformer", Unit (fun x -> use_init := false), "Use nonstandard transformer: F(X) = X join T(X)"
   ] (fun f -> input_file := Some f)
     "Abstract interpreter for MCMT files.");
  let in_ch = create_channel_in !input_file in
  let parsed = parse in_ch in
  close_in in_ch;
  mcmt_to_ts parsed
  |> fun x -> List.iter print_transition_system x; x
  |> List.map (eval_mcmt_prog 1000 !num_iterations !use_init)
  |> List.fold_left (fun x y -> x^"\n"^y) ""
  |> fun x -> printf "%s@." x; x
  |> add_learned !input_file;;
