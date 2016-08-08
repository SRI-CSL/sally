open Simple_ast;;

let rec string_of_simple = function
  | Nat i -> string_of_int i
  | Int i -> string_of_int i
  | Float f -> string_of_float f
  | Ident str -> str
  | Constrained f -> "{ `a | "^string_of_simple (f (Ident "`a")) ^ " }"
  | Add (e1, e2) -> "("^(string_of_simple e1)^" + "^(string_of_simple e2)^")"
  | Sub (e1, e2) -> "("^(string_of_simple e1)^" - "^(string_of_simple e2)^")"
  | Mul (e1, e2) -> "("^(string_of_simple e1)^" * "^(string_of_simple e2)^")"
  | Div (e1, e2) -> "("^(string_of_simple e1)^" / "^(string_of_simple e2)^")"
  | Ge (e1, e2) -> "("^(string_of_simple e1)^" >= "^(string_of_simple e2)^")"
  | Gt (e1, e2) -> "("^(string_of_simple e1)^" > "^(string_of_simple e2)^")"
  | Eq (e1, e2) -> "("^(string_of_simple e1)^" = "^(string_of_simple e2)^")"
  (*| Neq (e1, e2) -> "("^(string_of_simple e1)^" != "^(string_of_simple e2)^")"*)
  | Not e -> "( not "^(string_of_simple e)^")"
  | And (e1, e2) -> "("^(string_of_simple e1)^" and "^(string_of_simple e2)^")"
  | Or (e1, e2) -> "("^(string_of_simple e1)^" or "^(string_of_simple e2)^")"
  | Assign (e1, e2) -> (string_of_simple e1)^" := "^(string_of_simple e2)
  | Cond (e1, e2, e3) -> "(if "^(string_of_simple e1)^" then "^(string_of_simple e2)^" else "^(string_of_simple e3)^")"
  | True -> "true"
  | False -> "false"
  | Seq (e::es) -> (string_of_simple e)^"; "^(string_of_simple (Seq es))
  | Seq [] -> ""
  | Branch (e::es) -> "("^(string_of_simple e)^")\n||\n"^(string_of_simple (Branch es))
  | Branch [] -> ""
  | Local (decl, e) ->
      match decl with
      | Nat_decl str -> "(let "^str^" : nat in "^(string_of_simple e)^")"
      | Int_decl str -> "(let "^str^" : int in "^(string_of_simple e)^")"
      | Real_decl str -> "(let "^str^" : real in "^(string_of_simple e)^")"
      | Bool_decl str -> "(let "^str^" : bool in "^(string_of_simple e)^")"
      | Enum_def (enum, _) -> "(let "^enum^" : enum in "^(string_of_simple e) ^")"
      | Enum_decl (str, enum) -> "(let "^str^" : "^enum^" in "^(string_of_simple e) ^")"
      | Constraint_decl (decl, e) -> string_of_simple e ^ " with ("^string_of_simple e^")"

