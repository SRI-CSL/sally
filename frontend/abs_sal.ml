open Abs.Sal_to_simple_ast;;
open Abs.Simple_ast;;
open Abs.Print_simple;;
open Abs.Interpret_simple;;
open Abs.Inline;;
open Bddapron;;
open Format;;

exception Malformed_sal_prog;;

let manbox = Box.manager_alloc ();;
let manoct = Oct.manager_alloc ();;
let manpk = Polka.manager_alloc_strict ();;

let print_expression_list es =
  List.iter (fun ex -> printf "    %s\n" (string_of_simple ex)) es;;

let print_sal_prog p =
  printf "%s\n" "initials: ";
  (match p.initials with
   | Seq es -> print_expression_list es
   | e -> printf "    %s\n" (string_of_simple e));
  let print_guarded (e, es) =
    printf "guard: %s\n" (string_of_simple e);
    (match es with
     | Seq es -> print_expression_list es
     | _ -> raise Malformed_sal_prog) in
  List.iter print_guarded p.guarded;
  printf "%s\n" "default:";
  (match p.default with
   | None -> printf "    %s\n" "none"
   | Some (Seq es) -> print_expression_list es
   | _ -> raise Malformed_sal_prog);;

let rec eval_step man env inv cond p ctx' =
  let string_from_decl = function
    | Nat_decl str -> str
    | Int_decl str -> str
    | Real_decl str -> str
    | Bool_decl str -> str
    | Enum_decl (str, _) -> str
    | _ -> raise Malformed_sal_prog in
  let current = List.map string_from_decl p.state_vars in
  let next = List.map string_from_decl p.next_state_vars in
  let next_exprs = List.map (Expr1.var env cond) next in
  let assigned = Domain1.assign_lexpr man cond ctx' current next_exprs None in
  Domain1.forget_list man assigned next |> Domain1.meet man inv

and

eval_sal man env cond inv ctx p lim cnt =
  let guards = List.map (fun g -> Domain1.meet_condition man cond ctx (Expr1.Bool.of_expr (fst g |> make_expr1 env cond))) p.guarded in
  List.iter (printf "guard: %a@." (Expr1.Bool.print cond)) guards;
  let all_guards_false = List.fold_left (&&) true (List.map (Domain1.is_bottom man) guards) in
  printf "all guards false: %s\n" (string_of_bool all_guards_false);
  let any_guards_true = List.fold_left (||) false (List.map (Domain1.is_eq man ctx) guards) in
  printf "any guards true: %s\n" (string_of_bool any_guards_true);
  let ctx' =
    if not (all_guards_false) (* do not go straight to ELSE *)
    then
      let guarded_to_cond (e, es) = Cond (e, es, p.no_transition) in
      let guardeds = List.map (fun x -> interpret man env cond ctx (guarded_to_cond x)) p.guarded in
      (*List.iter (printf "guarded: %a@." (Domain1.print man)) guardeds;*)
      let evaluated_guardeds = List.fold_left (Domain1.join man) (Domain1.bottom man env) guardeds in
      if any_guards_true (* check if some guards are definitely true *)
      then evaluated_guardeds (* ELSE does not get executed *)
      else (* ELSE may be executed *)
        match p.default with
          | None -> evaluated_guardeds
          | Some e -> Domain1.join man evaluated_guardeds (interpret man env cond ctx e)
    else (* all guards are definitely false *)
      match p.default with
      | None -> interpret man env cond ctx p.no_transition
      | Some e -> interpret man env cond ctx e in
  let ctx' = Domain1.join man (eval_step man env inv cond p ctx') ctx in
  (* printf "ctx': %a@." (Domain1.print man) ctx'; *)
  if (Domain1.is_eq man ctx ctx')
  then ctx
  else if cnt = 0
  then eval_sal man env cond inv (Domain1.widening man ctx ctx') p lim lim
  else eval_sal man env cond inv ctx' p lim (cnt - 1);;

let eval_sal_prog p =
  let decls = p.constants @ p.state_vars @ p.next_state_vars in
  let invs = p.invariants in
  let (man, env, cond, ctx) = initialize decls invs in
  let init = interpret man env cond ctx p.initials in
  printf "initial state: %a@." (Domain1.print man) init;
  let res = eval_sal man env cond ctx init p 5 5 in
  printf "invariants found: %a@." (Domain1.print man) res;;
    
let create_channel_in = function
  | Some filename -> open_in filename
  | None -> stdin

let _ =
  let input_file = ref None in
  (let open Arg in
   Arg.parse [] (fun f ->
       input_file := Some f) "");
  create_channel_in !input_file
  |> Io.Sal_lexer.parse
  |> inline
  |> sal_to_progs;
  |> fun p -> print_sal_prog p; eval_sal_prog p;;
