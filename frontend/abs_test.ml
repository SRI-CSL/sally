open Abs.Simple_ast;;
open Abs.Interpret_simple;;

let gen_expr cst expr_fun =
  let rec repeat expr_fun res = function
    | 0 -> res
    | cst -> repeat expr_fun (expr_fun cst::res) (cst - 1) in
  repeat expr_fun [] cst;;

(* generate a test program of configurable size to find invariants for *)
let test_prog num =
  let decls =
    ( Real_decl "x" ::
      Real_decl "y" ::
      Real_decl "z" ::
      (gen_expr num (fun x -> Bool_decl ("bool"^(string_of_int x))))) in
  let invs = [] in
  let expr =
    Seq
    (Assign (Ident "x", Nat 1) ::                                   (* x := 1; *)
     Assign (Ident "y", Nat 0) ::                                   (* y := 0; *)
     Assign (Ident "z", Nat 0) ::                                   (* z := 0; *)
     (List.flatten ( gen_expr num                                   (* repeat for num times: *)
        (fun x ->
        ([Cond (Ident ("bool"^(string_of_int x)),                     (* if a boolean of unknown value is true *)
                Assign (Ident "y", Add (Ident "x", Nat 2)),           (* then y := x + 2 *)
                Assign (Ident "z", Mul (Ident "x", Nat 2)));          (* else z := x * 2; *)
              Assign (Ident "x", Add (Ident "y", Ident "z"))]))))) in (* x := y + z; *)
  { decls; invs; expr };;

(* in this case, not learning from conditionals (especially because there is nothing useful to learn)
   and using the Oct manager allows for larger programs *)
let _ = interpret_program false (Oct.manager_alloc()) (test_prog 600);;
