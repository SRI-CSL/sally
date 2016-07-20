open Types;;
open Apron;;
open Format;;

(* printing *)
let print_guarded g =
  printf "guard: %a@, expr: %a@." Abstract1.print g.guard Abstract1.print g.expr;;

let print_transition trans =
  match trans with
  | Assignment a    -> printf "transition = %a@." Abstract1.print a
  | Guarded (gs, e) ->
      printf "%s =" "transition";
      List.map print_guarded gs;
      printf "else = %a@." Abstract1.print e;;

let print_trans_sys { vars; env; invs; init; trans } =
  printf "invs=%a@.init=%a@." Abstract1.print invs Abstract1.print;
  print_transition trans;;

(* effectively map over a lincons earray *)
let earray_map f arr =
  let len = Lincons1.array_length arr in
  let new_arr = Lincons1.array_make (Lincons1.array_get_env arr) len in
  let rec exec i =
    if i = len
      then new_arr
      else
        (Lincons1.array_set new_arr i (f (Lincons1.array_get arr i));
        exec (i + 1)) in
  exec 0;;

(* negate coefficients of a linear constraint (side-effecting) *)
let negate_coeffs lincons =
  let env = Lincons1.get_env lincons in
  let vars =
    let (ints, reals) = Environment.vars env in
      (Array.to_list ints) @ (Array.to_list reals) in
  let negated_coeff lincons v = (Coeff.neg (Lincons1.get_coeff lincons v), v) in
  let negated_coeffs = List.map (negated_coeff lincons) vars in
  let negated_cst = Coeff.neg (Lincons1.get_cst lincons) in
  Lincons1.set_list lincons negated_coeffs (Some negated_cst);;

(* invert linear constraints (except for EQMOD) *)
exception Cannot_invert of string;;

let not_lincons lincons =
  let inverted = Lincons1.copy lincons in
  match Lincons1.get_typ lincons with
  | Lincons1.EQ    -> Lincons1.set_typ inverted Lincons1.DISEQ; inverted
  | Lincons1.SUPEQ -> negate_coeffs inverted; Lincons1.set_typ inverted Lincons1.SUP; inverted
  | Lincons1.SUP   -> negate_coeffs inverted; Lincons1.set_typ inverted Lincons1.SUPEQ; inverted
  | Lincons1.DISEQ -> Lincons1.set_typ inverted Lincons1.EQ; inverted
  | _ -> raise (Cannot_invert "Cannot invert this linear constraint typ");;

(* operations on conds *)
let not_cond c =
  let env = Abstract1.env c in
  let man = Abstract1.manager c in
  Abstract1.of_lincons_array man env (earray_map not_lincons (Abstract1.to_lincons_array man c))

let and_cond c1 c2 = Abstract1.meet (Abstract1.manager c1) c1 c2;;

let or_cond c1 c2 = Abstract1.join (Abstract1.manager c1) c1 c2;;

let and_conds cs =
  let cs_arr = Array.of_list cs in
  Abstract1.meet_array (Abstract1.manager cs_arr.(0)) cs_arr;;

let or_conds cs =
  let cs_arr = Array.of_list cs in
  Abstract1.join_array (Abstract1.manager cs_arr.(0)) cs_arr;;

let is_lt c1 c2 =
  let man = Abstract1.manager c1 in
  (Abstract1.is_leq man c1 c2) && (not (Abstract1.is_eq man c1 c2));;

(* operations on guardeds *)
let flatten_guarded g =
  and_cond g.guard g.expr;;
