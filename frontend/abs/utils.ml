open Types;;
open Apron;;
open Format;;

let print_trans_sys { vars; env; invs; init; transition } =
  printf "invs=%a@.init=%a@.transition=%a@." Abstract1.print invs Abstract1.print init Abstract1.print transition;;

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
  Lincons1.set_list lincons [] (Some negated_cst);;

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

(* operations on guardeds *)

(* guardeds with ELSE *)
let else_guard guardeds else_expr man env =
  let len = List.length guardeds in
  let neg_arr = Array.make len (Abstract1.top man env) in
  let rec fill_neg_arr gs i =
    match gs with
    | [] -> ()
    | g::gs -> neg_arr.(i) <- not_cond (g.guard); fill_neg_arr gs ( i + 1 ) in
  { guard = Abstract1.meet_array man neg_arr; expr = else_expr }::guardeds;;

(* nested if-then-else *)
let cond_guard guardeds else_expr man env =
  let rec add_negated gs negs added =
    match gs with
    | []    -> { guard = negs; expr = else_expr }::added
    | g::gs -> 
        add_negated gs (and_cond (not_cond g.guard) negs)
          ({ g with guard = and_cond negs g.guard }::added) in
  add_negated guardeds (Abstract1.top man env) [];;

(* operations on expressions *)
exception Cannot_extract of string;;

let extract_guarded expr =
  match expr with
  | Guarded g -> g
  | _ -> raise (Cannot_extract "Not a Guarded expression");;

let extract_abs expr =
  match expr with
  | Abs a -> a
  | _ -> raise (Cannot_extract "Not an Abs expression");;

(* turn expression into an abstract variable *)
let rec flatten expr =
  let to_abs g = and_cond g.guard (flatten g.expr) in
  match expr with
  | Guarded g -> to_abs g
  | Guardeds gs -> or_conds (List.map to_abs gs)
  | Abs a -> a;;
   
