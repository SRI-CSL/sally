open Types;;
open Apron;;
open Format;;

let print_trans_sys { vars; env; invs; init; transition } =
  printf "invs=%a@.init=%a@.transition=%a@." Abstract1.print invs Abstract1.print init Abstract1.print transition;;

(* effectively map over a lincons earray *)
let earray_map arr f =
  let len = Lincons1.array_length arr in
  let new_arr = Lincons1.array_make (Lincons1.array_get_env arr) len in
  let rec exec i =
    if i = len
      then new_arr
      else
        (Lincons1.array_set new_arr (f (Lincons1.array_get arr i));
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
  | Lincons1.SUPEQ -> negate_coeffs inverted; inverted
  | Lincons1.SUP   -> negate_coeffs inverted; inverted
  | Lincons1.DISEQ -> Lincons1.set_typ inverted Lincons1.EQ; inverted
  | _ -> raise (Cannot_invert "Cannot invert this linear constraint typ");;

(* operations on conds *)

let and_cond c1 c2 man =
  { constrained = c1.constrained @ c2.constrained
  ; abs         = Abstract1.meet man c1.abs c2.abs };;

let or_cond c1 c2 man =
  { constrained = c1.constrained @ c2.constrained
  ; abs         = Abstract1.join man c1.abs c2.abs };;

(* operations on guardeds *)


(* nested if-then-else *)
  
