open Bddapron;;
open Format;;

exception Unexpected_lincons;;
exception Backtrack;;

(* Convert a BDD into an mcmt string *)
let rec string_of_bdd env ls = function
  | Cudd.Bdd.Bool true -> if ls = [] then "" else "( "^(List.fold_left (fun x y -> x^" "^y) "and" ls)^")"
  | Cudd.Bdd.Bool false -> raise Backtrack
  | Cudd.Bdd.Ite (i, b1, b2) ->
      try string_of_bdd env ((PMappe.find i env.Bdd.Env.idcondvar)::ls) (Cudd.Bdd.inspect b1) with
      _ -> try string_of_bdd env ((PMappe.find i env.Bdd.Env.idcondvar)::ls) (Cudd.Bdd.inspect b2) with
           _ -> raise Backtrack;;

(* Convert an apron linear constraint into an mcmt string *)
let string_of_lincons env lc =
  (* Convert APRON typ *)
  let string_of_typ = function
    | Apron.Lincons0.EQ -> "="
    | Apron.Lincons0.SUPEQ -> ">="
    | Apron.Lincons0.SUP -> ">"
    | Apron.Lincons0.DISEQ -> "/="
    | Apron.Lincons0.EQMOD _ -> raise Unexpected_lincons in
  (* Get a linear constraint's coefficient as a string *)
  let get_coeff_str = function
    | Apron.Coeff.Scalar s -> Apron.Scalar.to_string s
    | _ -> raise Unexpected_lincons in
  (* Side-effecting function:
       string_of_term res coeff dim
     converts the term (coeff * dim) into an mcmt string
     assigned to res *)
  let string_of_term res coeff dim =
    let apron_env = env.Bdd.Env.ext.Bddapron.Env.eapron in
    let coeff_str = get_coeff_str coeff in
    let coeff = float_of_string coeff_str in
    if coeff = 0.0 then ()
    else if coeff = 1.0 then res := (Apron.Environment.var_of_dim apron_env dim |> Apron.Var.to_string)::(!res)
    else res := ("( * "^coeff_str^" "^(Apron.Environment.var_of_dim apron_env dim |> Apron.Var.to_string)^" )")::(!res) in
  (* Convert a list of term strings into an mcmt string giving their sum *)
  let rec sum = function
    | s1::s2::ss -> sum (("( + "^s1^" "^s2^" )")::ss)
    | [s] -> s
    | [] -> "" in
  (* Convert a linear expression into a string *)
  let string_of_linexpr le =
    let str = ref [] in
    Apron.Linexpr0.iter (string_of_term str) le;
    let res = sum !str in
    let cst = Apron.Linexpr0.get_cst le |> get_coeff_str in
    if (float_of_string cst) = 0.0 then res else "( + "^res^" "^cst^" )" in
  "( "^(string_of_typ lc.Apron.Lincons0.typ)^" "^(string_of_linexpr lc.Apron.Lincons0.linexpr0)^" 0 )";;

(* Convert a bddapron domain representing the invariants for a transition system into an mcmt assume string:
     mcmt_of_domain name man apron_man env res
   results in the string for the transition system called name with invariants contained in the domain res,
   where man, apron_man, and env are respectively the bddapron Manager, the apron Manager, and the bddapron Env
   used to find the invariants *)
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

let create_channel_in = function
  | Some filename -> open_in filename
  | None -> stdin;;

let create_channel_out = function
  | Some filename -> open_out filename
  | None -> stdout;;

(* Add strings representing learned invariants to the original mcmt file just
   before the first query definition:
     add_learned "in.mcmt" learned
   adds the invariant strings in learned to the program in file "in.mcmt", outputting the result
   to a new file "in_learned.mcmt" *)
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
