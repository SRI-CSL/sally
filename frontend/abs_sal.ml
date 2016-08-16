open Abs.Sal_to_simple_ast;;
open Abs.Simple_ast;;
open Abs.Sal_simple_ast;;
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

(* evaluate a guarded command; if the guard is false, then the result is bottom *)
eval_guarded man env cond inv ctx (g, c) =
  let guard = Expr1.Bool.of_expr (make_expr1 env cond g) in
  let ctx = Domain1.meet_condition man cond ctx guard in
  interpret true man env cond inv ctx c

and

eval_sal man env cond inv ctx p lim cnt =
  let guards = List.map (fun g -> Domain1.meet_condition man cond ctx (Expr1.Bool.of_expr (fst g |> make_expr1 env cond))) p.guarded in
  let all_guards_false = List.fold_left (&&) true (List.map (Domain1.is_bottom man) guards) in
  let any_guards_true = List.fold_left (||) false (List.map (Domain1.is_eq man ctx) guards) in
  let ctx's =
    if not (all_guards_false) (* do not go straight to ELSE *)
    then
      let guardeds = List.map (fun x -> (eval_guarded man env cond inv ctx x, x)) p.guarded in
      if any_guards_true (* check if some guards are definitely true *)
      then guardeds (* ELSE does not get executed *)
      else (* ELSE may be executed *)
        match p.default with
          | None -> guardeds
          | Some e -> (interpret true man env cond inv ctx e, (True, e))::guardeds
    else (* all guards are definitely false *)
      match p.default with
      | None -> [(interpret true man env cond inv ctx p.no_transition, (True, p.no_transition))]
      | Some e -> [(interpret true man env cond inv ctx e, (True, e))] in
  let ctx's = List.map (fun (x, y) -> (Domain1.join man (eval_step man env inv cond p x) ctx, y)) ctx's in
  let ctx' = List.fold_left (Domain1.join man) (Domain1.bottom man env) (List.map fst ctx's) in
  printf "ctx': %a@." (Domain1.print man) ctx';
  if (Domain1.is_eq man ctx ctx')
  then ctx
  else if cnt = 0
  then
    let widened = eval_sal man env cond inv (Domain1.widening man ctx ctx') p lim lim in
    (* Cannot do narrowing for all guarded commands; must figure out which guarded commands resulted in the
       need for widening and do narrowing using only those *)
    let to_redo = List.filter (fun (x, _) -> not (Domain1.is_eq man ctx x)) ctx's in (* which guarded commands resulted in widening? *)
    let narrow = List.map (fun (_, y) -> eval_step man env inv cond p (eval_guarded man env cond inv widened y)) to_redo in (* one more pass through *)
    let narrowed = List.fold_left (Domain1.join man) ctx' narrow in (* join them together *)
    eval_sal man env cond inv narrowed p lim lim
  else eval_sal man env cond inv ctx' p lim (cnt - 1);;

let eval_sal_prog p =
  let decls = p.constants @ p.state_vars @ p.next_state_vars in
  let invs = p.invariants in
  let (man, env, cond, ctx) = initialize (Polka.manager_alloc_strict()) decls invs 500 in
  let init = interpret true man env cond ctx ctx p.initials in
  printf "initial state: %a@." (Domain1.print man) init;
  let res = eval_sal man env cond ctx init p 6 6 in
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
  |> sal_to_progs
  |> fun p -> print_sal_prog p; eval_sal_prog p;;
