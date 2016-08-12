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

let mcmt_of_domain name man apron_man env res =
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
  "( assume "^name^" "^
    (if List.length results < 2
    then List.hd results
    else "( "^(List.fold_left (fun x y -> x^" "^y) "or" results)^" )")
  ^" )";;

let rec eval_mcmt_prog cond_size ts =
  let decls = ts.decls @ ts.current_sv_decls @ ts.next_sv_decls in
  let invs = ts.invs in
  let apron_man = Polka.manager_alloc_strict() in
  try (
    let (man, env, cond, ctx) = initialize apron_man decls invs cond_size in
    printf "invariant: %a@." (Domain1.print man) ctx;
    let init = interpret true man env cond ctx ctx ts.init in
    printf "initial state: %a@." (Domain1.print man) init;
    let res = eval_mcmt man env cond ctx init ts 5 5 in
    mcmt_of_domain ts.name man apron_man env res)
  with Bdd.Env.Bddindex -> eval_mcmt_prog (cond_size * 2) ts;;

let print_transition_system ts =
  printf "Transition system: %s\n" ts.name;
  List.iter (fun x -> printf "Invariant: %s\n" (string_of_simple x)) ts.invs;
  printf "Initial:%s\n" (string_of_simple ts.init);
  printf "Transition:%s\n" (string_of_simple ts.trans);;


let create_channel_in = function
  | Some filename -> open_in filename
  | None -> stdin;;

let create_channel_out = function
  | Some filename -> open_out filename
  | None -> stdout;;

let add_learned in_name learned =
  let rec check_query str start =
    try
      (if (String.sub str start 5) = "query"
       then true
       else check_query str (start + 1))
    with Invalid_argument _ -> false in
  let rec separate_at_query found pre post in_ch =
    try 
      (let str = input_line in_ch in
       if found
       then separate_at_query found pre (post^"\n"^str) in_ch
       else if check_query str 0
       then separate_at_query true pre (post^"\n"^str) in_ch
       else separate_at_query false (pre^"\n"^str) post in_ch)
   with End_of_file -> close_in in_ch; (pre, post) in 
  let out_name =
    match in_name with
    | Some name -> Some ((String.sub name 0 (String.length name - 5))^"_learned.mcmt")
    | None -> None in
  let out_ch = create_channel_out out_name in
  let (lines_before, lines_after) =
    separate_at_query false "" "" (create_channel_in in_name) in
  output_string out_ch (lines_before^learned^"\n"^lines_after);
  close_out out_ch;;

let _ =
  let input_file = ref None in
  (let open Arg in
   Arg.parse [] (fun f ->
       input_file := Some f) "");
  let in_ch = create_channel_in !input_file in
  let parsed = parse in_ch in
  close_in in_ch;
  mcmt_to_ts parsed
  |> fun x -> List.iter print_transition_system x; x
  |> List.map (eval_mcmt_prog 1000)
  |> List.fold_left (fun x y -> x^"\n"^y) ""
  |> fun x -> printf "%s@." x; x
  |> add_learned !input_file;;
