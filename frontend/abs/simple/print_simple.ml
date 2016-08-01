open Simple_ast;;

let rec string_of_simple = function
  | Nat i -> string_of_int i
  | Int i -> string_of_int i
  | Float f -> string_of_float f
  | Ident str -> str
  | Constrained f -> "{ a | "^string_of_simple (f (Ident "x")) ^ " }"
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
