open Abs.Sal_to_simple_ast;;
open Abs.Simple_ast;;
open Abs.Print_simple;;
open Abs.Simple_to_abs;;
open Abs.Inline;;
open Apron;;
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

let rec eval_step man p ctx ctx' =
  let ctx' = Abstract1.change_environment man ctx' ctx.Abstract1.env false in
  let current = List.map (function | Nat_decl str -> Var.of_string str | Int_decl str -> Var.of_string str | Real_decl str -> Var.of_string str | Bool_decl str -> Var.of_string str) p.state_vars in
  let next = List.map (function | Nat_decl str -> Var.of_string str | Int_decl str -> Var.of_string str | Real_decl str -> Var.of_string str | Bool_decl str -> Var.of_string str) p.next_state_vars in
  let ctx_swap = Abstract1.rename_array man ctx' (Array.of_list (current @ next)) (Array.of_list (next @ current)) in
  Abstract1.forget_array man ctx_swap (Array.of_list next) false |> Abstract1.join man ctx

and

eval_sal man ctx p lim cnt =
  let evaluated_guards = List.map (fun x -> from_expr man ctx (Var.of_string "tmp") (fst x)) p.guarded in
  (*List.iter (printf "guard: %a@." Abstract1.print) evaluated_guards;
  let or_guards = Abstract1.join_array man (Array.of_list evaluated_guards) in
  printf "or: %a@." Abstract1.print or_guards; *)
  let all_guards_false = Abstract1.meet man (from_expr man ctx (Var.of_string "tmp") True) (Abstract1.join_array man (Array.of_list evaluated_guards)) |> Abstract1.is_bottom man in
  (* printf "all false: %s\n" (string_of_bool all_guards_false); *)
  let ctx' =
    if not (all_guards_false)
    then
      let guarded_to_cond (e, es) = Cond (e, es, p.no_transition) in
      let guardeds = List.map (fun x -> from_expr man ctx (Var.of_string "tmp") (guarded_to_cond x)) p.guarded in
      let exprs =
          match p.default with
          | None -> guardeds
          | Some e -> (from_expr man ctx (Var.of_string "tmp") e)::guardeds in
      (*List.iter (fun x -> (printf "%s\n" "expr"; (Array.iter (fun y -> printf "int %s\n" (Var.to_string y)) (Environment.vars x.Abstract1.env |> fst)))) exprs;
      List.iter (printf "expr: %a@." Abstract1.print) exprs;
      List.iter (printf "expr': %a@." Abstract1.print) (List.map (eval_step man p ctx) exprs);*)
      Abstract1.join_array man (Array.of_list (List.map (eval_step man p ctx) exprs))
    else
      match p.default with
      | None -> ctx
      | Some e -> eval_step man p ctx (from_expr man ctx (Var.of_string "tmp") e) in
  printf "ctx': %a@." Abstract1.print ctx';
  if (Abstract1.is_eq man ctx ctx')
  then ctx
  else if cnt = 0
  then eval_sal man (Abstract1.widening man ctx ctx') p lim lim
  else eval_sal man ctx' p lim (cnt - 1);;

let eval_sal_prog man p =
  let (env, invs) = from_decls (p.constants @ p.state_vars @ p.next_state_vars) in
  let lincons_arr = Lincons1.array_make env (List.length invs) in
  List.iteri (fun i lc -> Lincons1.array_set lincons_arr i lc) invs;
  let ctx = Abstract1.of_lincons_array man env lincons_arr in
  let ctx' = Abstract1.change_environment man (from_expr man ctx (Var.of_string "tmp") (p.initials)) env false in
  eval_sal man ctx' p;;
    
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
  |> fun p -> print_sal_prog p; eval_sal_prog manpk p 5 5
  |> printf "invariants found: %a@." Abstract1.print; (* print_sal_prog *)
