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

(**
  Does fixpoint computation:
  - start from [prev]
  - iterate while [while_op] holds for [prev] and [curr]
  - it does at most [iter_count] iterations, or to completion if [iter_count] <= 0

 Notes for iteration: keep iterating while
  - for fixpoint: go while !=
  - for widening: go while <
  - for narrowing: go while >

 [iter_combine] is usually (fun x y -> y) for regular iteration, or the widening/narrowing operator.
*)

let rec mcmt_iterate man env cond inv init prev ts while_op iter_count iter_combine =
  let curr =
    (** Interpret one-step transition (keeps variables) *)
    interpret man env cond inv prev ts.trans |>
    (** Just keep the next-state variables *)
    eval_step man env inv cond ts |>
    (** Join with initial states *)
    Domain1.join man init in
  let compare = while_op prev curr in
    printf "prev: %a@." (Domain1.print man) prev;
    printf "curr: %a@." (Domain1.print man) curr;
    if compare && (iter_count != 1) then
      let combined = iter_combine prev curr in
      mcmt_iterate man env cond inv init combined ts while_op (iter_count-1) iter_combine
    else prev, curr, compare

(** Evaluate a transition relation until a fixed point is found:
      [ eval_mcmt man env cond inv ctx ts cnt ]
    will repeatedly apply the transition relation [ts] to the current context [ctx] using
    [man], [env], and [cond];
    move forward one step in the transition relation;
    apply the invariants [inv] to the new domain; and
    decrement [cnt]. When [cnt = 0], widening and narrowing are performed. *)
let eval_mcmt man env cond inv init ts fixpoint_iter narrowing_iter =
  let ai_neq = (fun x y -> not (Domain1.is_eq man x y)) in
  let ai_lt = (fun x y -> not (Domain1.is_leq man y x)) in (** x < y as !(x >= y) *)
  let ai_gt = (fun x y -> not (Domain1.is_leq man x y)) in (** x > y as !(x <= y) *)
  (* Do fixpoint computation for fixpont_iter iterations: go while != *)
  let trans_prev, trans_curr, trans_is_neq =
    printf "Iterating for %s\n" "fixpoint";
    mcmt_iterate man env cond inv init init ts ai_neq fixpoint_iter (fun x y -> y) in
  if not trans_is_neq then trans_curr (* double negation: we're fixpoint *)
  else
    (* We're not a fixpoint, do widening: go while wid_prev < wid_curr, wid_prev is always widening *)
    let wid_prev, wid_curr, _ =
      printf "Iterating for %s\n" "widening";
      mcmt_iterate man env cond inv init trans_curr ts ai_lt (-1) (Domain1.widening man) in
    if narrowing_iter = 0 then wid_prev
    else if narrowing_iter = 1 then wid_curr
    else
      (* We already did one step, do narrowing-1 iterations. We know wid_prev >= wid_curr.
         Go while nar_prev > nra_curr, nar_cur is the one we return  *)
      let nar_prev, nar_curr, _ =
        printf "Iterating for %s\n" "narrowing";
        mcmt_iterate man env cond inv init wid_curr ts ai_gt (narrowing_iter-1) (fun x y -> y) in
      nar_curr

(** Find invariants for a transition system in an mcmt program:
      [ eval_mcmt_prog cond_size fixpoint_iter narrowing_iter use_init ts ]
    Finds invariants for transition system [ts] by doing:
     * fixpoint computation unitl fixpoint is found or [fixpoint_iter] is exceeded,
     * if no fixpoint is found then:
       - do widening to find a post-fixpoint,
       - do 'narrowing' until a fixpoint is found of [narrowing_iter] is exceeded.
    The [cond_size] decides the initial size for the condition BDD and [use_init] determines whether
    the result from taking one step of the transition is joined with the
    initial state or the previous state. If [cond_size] is too small,
    its size is doubled, and [eval_mcmt_prog] begins again. *)
let rec eval_mcmt_prog cond_size fixpoint_iter narrowing_iter ts =
  let decls = ts.decls @ ts.current_sv_decls @ ts.next_sv_decls in
  let invs = ts.invs in
  let apron_man = Polka.manager_alloc_strict() in
  try (
    let (man, env, cond, invariant) = initialize apron_man decls invs cond_size in
    printf "invariant: %a@." (Domain1.print man) invariant;
    let init = interpret man env cond invariant invariant ts.init in
    printf "initial state: %a@." (Domain1.print man) init;
    let res = eval_mcmt man env cond invariant init ts fixpoint_iter narrowing_iter in
    mcmt_of_domain ts.name man apron_man env res)
  with Bdd.Env.Bddindex -> eval_mcmt_prog (cond_size * 2) fixpoint_iter narrowing_iter ts;;

(** [ print_transition_system ts ] prints the transition system [ts]
    after it has been converted into simple ASTs *)
let print_transition_system ts =
  printf "Transition system: %s\n" ts.name;
  List.iter (fun x -> printf "Invariant: %s\n" (string_of_simple x)) ts.invs;
  printf "Initial:%s\n" (string_of_simple ts.init);
  printf "Transition:%s\n" (string_of_simple ts.trans);;

let () =
  let input_file = ref None in
  let fixpoint_iterations = ref 10 in
  let narrowing_iterations = ref 1 in
  (let open Arg in
   Arg.parse [
     "--fixpoint-iterations", Int (fun x -> fixpoint_iterations := x),
        Printf.sprintf "Limit on the number of iterations to use for fixpoint computation (default %d)" !fixpoint_iterations;
     "--narrowing-iterations", Int (fun x -> narrowing_iterations := x),
           Printf.sprintf "Limit on the number of 'narrowing' steps to use (default %d)" !narrowing_iterations
   ] (fun f -> input_file := Some f)
     "Abstract interpreter for MCMT files.");
  let in_ch = create_channel_in !input_file in
  let parsed = parse in_ch in
  close_in in_ch;
  mcmt_to_ts parsed
  |> fun x -> List.iter print_transition_system x; x
  |> List.map (eval_mcmt_prog 1000 !fixpoint_iterations !narrowing_iterations)
  |> List.fold_left (fun x y -> x^"\n"^y) ""
  |> fun x -> printf "%s@." x; x
  |> add_learned !input_file;;
