open Ast.Sal_ast;;
open Abs.Types;;
open Abs.Utils;;
open Abs.Conversion;;
open Abs.Preproc;;

open Apron;;
open Mpqf;;
open Format;;

exception Unimplemented of string;;

let manbox = Box.manager_alloc ();;
let manpk = Polka.manager_alloc_strict ();;

(* set current-state values to next-state values and forget next-state constraints *)
let next_abs vars man abs =
  let current = vars.current_ints @ vars.current_reals in
  let next = vars.next_ints @ vars.next_reals in
  let renamed = Abstract1.rename_array man abs (Array.of_list (current @ next)) (Array.of_list (next @ current)) in
  Abstract1.forget_array man renamed (Array.of_list next) false;;

(* one step of the transition relation; stop stepping once fixed point reached or lim steps
   have been taken *)
let step_assigns ts pred lim =
  let transition = match ts.trans with Assignment a -> a in
  let rec stepper pred l =
    let next = Abstract1.meet ts.man ts.invs
               (Abstract1.join ts.man pred (next_abs ts.vars ts.man (Abstract1.meet ts.man transition pred))) in
      (* printf "step=%a@." Abstract1.print next; *)
      if (l > 0) then
        if Abstract1.is_eq ts.man next pred
          then (Abstract1.forget_array ts.man next (Array.of_list (ts.vars.next_ints @ ts.vars.next_reals)) false)
          else stepper next (l - 1)
        else stepper (Abstract1.widening ts.man pred next) lim in
  stepper pred lim;;

let step_guardeds ts pred lim =
  let rec stepper pred l = 
    let (gs, e) = match ts.trans with Guarded (gs, e) -> (gs, e) in
    let guard_passed g = not (Abstract1.is_bottom ts.man (and_cond pred g.guard)) in
    let guards_passed = List.filter (guard_passed) gs in
    let get_next assigns = Abstract1.meet ts.man ts.invs
               (Abstract1.join ts.man pred (next_abs ts.vars ts.man (Abstract1.meet ts.man assigns pred))) in
    let nexts = List.map get_next (List.map flatten_guarded guards_passed) in
    let next = if guards_passed = [] then get_next e else or_conds nexts in
    (*
    printf "step=%a@." Abstract1.print next;*)
    if (l > 0) then
      if Abstract1.is_eq ts.man next pred
      then (Abstract1.forget_array ts.man next (Array.of_list (ts.vars.next_ints @ ts.vars.next_reals)) false)
      else stepper next (l - 1)
    else stepper (Abstract1.widening ts.man pred next) lim in
  stepper pred lim;;
      
    

let step ts pred lim =
  match ts.trans with
  | Assignment a -> step_assigns ts pred lim
  | Guarded gs -> step_guardeds ts pred lim

(* from frontend *)
let create_channel_in = function
  | Some filename -> open_in filename
  | None -> stdin

let create_channel_out = function
  | Some filename -> open_out filename
  | None -> stdout

let _ =
  let input_file = ref None in
  (let open Arg in
   Arg.parse [] (fun f ->
       input_file := Some f) "");
  create_channel_in !input_file
  |> Io.Sal_lexer.parse
  |> preproc
  |> fun x -> handle_sal_defs x.definitions manpk
  |> List.map (fun ts -> step ts ts.init 100)
  |> List.map (printf "constraints found: %a@." Abstract1.print)
