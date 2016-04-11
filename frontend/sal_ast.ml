(*
 * ABTRACT SYNTAX FOR THE SIMPLIFIED SAL LANGUAGE
 *)
type state_var_tag = 
  | Local
  | Global
  | Input
  | Output

type assertion_tag =
  | Lemma
  | Theorem

type sal_type =
  | Base_type of string                         (* Primitive types *)
  | Range of sal_expr * sal_expr                (* [low .. high] *)
  | Enum of (string list)                       (* Enumeration/scalar type *)
  | Array of sal_type * sal_type                (* ARRAY index_type OF element_type *)
  | Subtype of string * sal_type * sal_expr     (* Predicate subtype *)

and sal_decl = (string list) * sal_type         (* name1, ..., name_k: type *)

and let_decl = string * sal_type * sal_expr     (* name : type = expr *)

and sal_expr =
  | Decimal of int
  | Float of float
  | Ident of string
  | Next of string
  | Funcall of string * (sal_expr list)
  | Array_access of sal_expr * sal_expr
  | Array_literal of string * sal_type * sal_expr
  | Set_literal of string * sal_type * sal_expr
  | Cond of ((sal_expr * sal_expr) list) * sal_expr  (* if-then-else *)
  | Opp of sal_expr
  | Add of sal_expr * sal_expr
  | Sub of sal_expr * sal_expr
  | Mul of sal_expr * sal_expr
  | Div of sal_expr * sal_expr
  | Ge of sal_expr * sal_expr
  | Gt of sal_expr * sal_expr
  | Le of sal_expr * sal_expr
  | Lt of sal_expr * sal_expr
  | Eq of sal_expr * sal_expr
  | Neq of sal_expr * sal_expr
  | Not of sal_expr
  | And of sal_expr * sal_expr
  | Or of sal_expr * sal_expr
  | Xor of sal_expr * sal_expr
  | Implies of sal_expr * sal_expr
  | Iff of sal_expr * sal_expr
  | Exists of sal_decl list * sal_expr
  | Forall of sal_decl list * sal_expr
  | Let of let_decl list * sal_expr

type state_var_decl = state_var_tag * (sal_decl list)

type sal_assignment =
  | Assign of sal_expr * sal_expr (* x = value or x' = value *)
  | Member of sal_expr * sal_expr (* x IN set of x' IN set *)

type guarded_command =
  | Guarded of sal_expr * (sal_assignment list)  (* expr -> assignments *)
  | Default of (sal_assignment list)             (* ELSE -> assignments *)

type sal_transition =
  | NoTransition                                 (* missing Transition clause *)
  | Assignments of sal_assignment list
  | GuardedCommands of guarded_command list

type sal_module = {
  state_vars: state_var_decl list;
  initialization: sal_assignment list;
  definition: sal_assignment list;
  invariant: sal_expr option;
  transition: sal_transition;
}
  
type sal_def = 
  | Type_decl of string
  | Type_def of string * sal_type
  | Constant_decl of string * sal_type
  | Constant_def of string * sal_type * sal_expr
  | Function_def of string * (sal_decl list) * sal_type * sal_expr
  | Assertion of string * assertion_tag * string * sal_expr
  | Module_def of string * sal_module

type sal_context = {
  ctx_name: string;
  definitions: sal_def list;
}



(*
 * PRETTY PRINTER
 *)
module F = Format

(* Operators and  precedences *)
module Op =
  struct
    type t = { name: string; precedence: int; }

    let negate  = { name = "-";   precedence = 10; }  (* Unary minus *)
    let div     = { name = "/";   precedence = 9; }
    let times   = { name = "*";   precedence = 9; }
    let minus   = { name = "-";   precedence = 8; }
    let plus    = { name = "+";   precedence = 8; }
    let ge      = { name = ">=";  precedence = 7; }
    let le      = { name = "<=";  precedence = 7; }
    let gt      = { name = ">";   precedence = 7; }
    let lt      = { name = "<";   precedence = 7; }
    let eq      = { name = "=";   precedence = 6; }
    let neq     = { name = "/=";  precedence = 6; }
    let _not    = { name = "NOT"; precedence = 5; }
    let _and    = { name = "AND"; precedence = 4; }
    let _or     = { name = "OR";  precedence = 3; }
    let _xor    = { name = "XOR"; precedence = 3; }
    let implies = { name = "=>";  precedence = 2; }
    let iff     = { name = "<=>"; precedence = 1; }

  end

(* Check whether op has lower precedence than l *)
let need_par op l = op.Op.precedence < l

let assertion_tag_to_string = function
  | Lemma -> "LEMMA"
  | Theorem -> "THEOREM"

let state_var_tag_to_string = function 
  | Local  -> "LOCAL"
  | Global -> "GLOBAL"
  | Input  -> "INPUT"
  | Output -> "OUTPUT"

let pp_string_list pp l =
  let rec loop = function
    | [] -> ()
    | [x] -> F.fprintf pp "%s" x
    | x :: r ->
	F.fprintf pp "%s,@ " x;
	loop r
  in
    F.fprintf pp "@[";
    loop l;
    F.fprintf pp "@]"


let rec pp_type pp = function
  | Base_type(name) ->
      F.fprintf pp "%s" name
  | Range(low,high) -> 
      F.fprintf pp "@[[%a .. %a]@]" pp_expr low pp_expr high
  | Enum(list) ->
      F.fprintf pp "@[{ %a }@]" pp_string_list list
  | Array(index,elem) ->
      F.fprintf pp "@[ARRAY %a OF %a@]" pp_type index pp_type elem
  | Subtype(var,base,pred) -> 
      F.fprintf pp "@[{ %s: %a |@ %a@ }@]" var pp_type base pp_expr pred

and pp_decls pp l =
  let rec loop = function
    | [] -> ()
    | [(vlist, ty)] -> F.fprintf pp "@[%a: %a@]" pp_string_list vlist pp_type ty
    | (vlist, ty) :: r ->
	F.fprintf pp "@[%a: %a@],@ " pp_string_list vlist pp_type ty;
	loop r
  in
    F.fprintf pp "@[";
    loop l;
    F.fprintf pp "@]"
	
and pp_expr pp expr =
  (*
   * pp ch l flg e:
   * - ch = output channel
   * - l = precedence of the enclosing operator (or 0)
   * - flg = right-most flag. If true, e is right most expression in its context.
   * - e = expresssion
   *)
  let rec pr0 = fun c -> pr c 0 true 

  and pr pp l flg = function
    | Decimal(x) -> F.fprintf pp "%d" x
    | Float(x) -> F.fprintf pp "%g" x
    | Ident(name) -> F.fprintf pp "%s" name
    | Next(name) -> F.fprintf pp "%s'" name
    | Funcall(name, arglist) ->
	F.fprintf pp "@[<hov2>%s(%a)@]" name pp_expr_list arglist
    | Array_access(array, index) ->
	F.fprintf pp "@[<hov2>%a[%a]@]" pr0 array pr0 index
    | Array_literal(var, ty, e) ->
	F.fprintf pp "@[<hov2>[[%s: %a]@ %a]@]" var pp_type ty pr0 e
    | Set_literal(var, ty, e) ->
	F.fprintf pp "@[<hov4>{ %s : %a |@ %a }@]" var pp_type ty pr0 e
    | Cond((c, e)::r, els) ->
	F.fprintf pp "@[<hv>";
	F.fprintf pp "@[IF %a@ THEN@;<1 2>%a@]@ " pr0 c pr0 e;
	List.iter (fun (c, e) -> F.fprintf pp "@[ELSIF %a@ THEN@;<1 2>%a@]@ "pr0 c pr0 e) r;
	F.fprintf pp "@[ELSE %a@ ENDIF@]" pr0 els;
        F.fprintf pp "@]"
    | Opp(e)      -> pp_unary pp l flg Op.negate e
    | Add(e1, e2) -> pp_binary pp l flg Op.plus e1 e2
    | Sub(e1, e2) -> pp_binary pp l flg Op.minus e1 e2
    | Mul(e1, e2) -> pp_binary pp l flg Op.times e1 e2
    | Div(e1, e2) -> pp_binary pp l flg Op.div e1 e2
    | Ge(e1, e2)  -> pp_binary pp l flg Op.ge e1 e2
    | Gt(e1, e2)  -> pp_binary pp l flg Op.gt e1 e2
    | Le(e1, e2)  -> pp_binary pp l flg Op.le e1 e2
    | Lt(e1, e2)  -> pp_binary pp l flg Op.lt e1 e2
    | Eq(e1, e2)  -> pp_binary pp l flg Op.eq e1 e2
    | Neq(e1, e2) -> pp_binary pp l flg Op.neq e1 e2
    | Not(e)      -> pp_unary  pp l flg Op._not e
    | And(e1, e2) -> pp_binary pp l flg Op._and e1 e2
    | Or(e1, e2)  -> pp_binary pp l flg Op._or e1 e2
    | Xor(e1, e2) -> pp_binary pp l flg Op._xor e1 e2
    | Implies(e1, e2) -> pp_binary pp l flg Op.implies e1 e2
    | Iff(e1, e2) -> pp_binary pp l flg Op.iff e1 e2
    | Exists(decls, e) ->
	if flg then
	  F.fprintf pp "@[<hov2>EXISTS (%a):@ %a@]" pp_decls decls pr0 e
	else
	  F.fprintf pp "@[<hov2>(EXISTS (%a):@ %a)@]" pp_decls decls pr0 e
    | Forall(decls, e) ->
	if flg then 
	  F.fprintf pp "@[<hov2>FORALL (%a):@ %a@]" pp_decls decls pr0 e
	else
	  F.fprintf pp "@[<hov2>(FORALL (%a):@ %a)@]" pp_decls decls pr0 e
    | Let(decls, e) ->
	if flg then 
	  F.fprintf pp "@[<hov2>LET %a IN@ %a@]" pp_let_decls decls pr0 e
	else
	  F.fprintf pp "@[<hov2>(LET %a IN@ %a)@]" pp_let_decls decls pr0 e
    | _ -> failwith "Print_expr: invalid expression"

  and pp_expr_list pp l =
    let rec loop = function
      | [] -> ()
      | [x] -> pr0 pp x
      | x :: r ->
	  pr0 pp x;
	  F.fprintf pp ",@ ";
	  loop r
    in
      F.fprintf pp "@[";
      loop l;
      F.fprintf pp "@]"

  and pp_unary pp l flg op e = 
    let sub_pr x = fun pp -> pr pp op.Op.precedence x in
      if need_par op l then
	F.fprintf pp "@[<hov1>(%s@ %a)@]" op.Op.name (sub_pr true) e
      else
	F.fprintf pp "@[<hov1>%s@ %a@]" op.Op.name (sub_pr flg) e

  and pp_binary pp l flg op e1 e2 = 
    let sub_pr x = fun pp -> pr pp op.Op.precedence x in
      if need_par op l then
	F.fprintf pp "@[<hov1>(%a@ %s@ %a)@]" (sub_pr false) e1 op.Op.name (sub_pr true) e2
      else
	F.fprintf pp "@[<hov1>%a@ %s@ %a@]" (sub_pr false) e1 op.Op.name (sub_pr flg) e2

  and pp_let_decls pp l =
    let rec loop = function
      | [] -> ()
      | [(name, ty, e)] -> F.fprintf pp "@[%s: %a = %a@]" name pp_type ty pr0 e
      | (name, ty, e) :: r ->
	  F.fprintf pp "@[%s: %a = %a@],@ " name pp_type ty pr0 e;
	  loop r
    in
      F.fprintf pp "@[<v>";
      loop l;
      F.fprintf pp "@]"
  in
    pr0 pp expr


(*
 * Function definition
 *)
let pp_fun_def pp name params ty body =
  F.fprintf pp "@[<hov2>%s(%a): %a =@ %a@];" name pp_decls params pp_type ty pp_expr body


(*
 * Lemma/theorem
 *)
let pp_assertion pp name tag module_name prop =
  F.fprintf pp "@[<hov2>%s: %s@ @[<hov2>%s |-@ %a@]@];" name (assertion_tag_to_string tag) module_name pp_expr prop


(*
 * Module
 *)
let rec pp_svar_decls pp l = 
  let rec loop = function
    | [] -> ()
    | [(vlist, ty)] -> F.fprintf pp "@[%a: %a@]" pp_string_list vlist pp_type ty
    | (vlist, ty) :: r ->
	F.fprintf pp "@[%a: %a@],@ " pp_string_list vlist pp_type ty;
	loop r
  in
    F.fprintf pp "@[<v>";
    loop l;
    F.fprintf pp "@]"
    
let pp_var_decl_section pp (section, decls) =
  F.fprintf pp "@[<v2>%s@," (state_var_tag_to_string section);
  pp_svar_decls pp decls;
  F.fprintf pp "@]@ "

let pp_state_var_decls pp l =
  List.iter (fun dcl -> pp_var_decl_section pp dcl) l

let pp_assignment pp = function
  | Assign(x,e) -> F.fprintf pp "@[<hov2>%a =@ %a@]; " pp_expr x pp_expr e
  | Member(x,e) -> F.fprintf pp "@[<hov2>%a IN@ %a@]; " pp_expr x pp_expr e


let rec pp_list_of_assignments pp = function
  | [] -> ()
  | [a] -> pp_assignment pp a
  | a :: r ->
      pp_assignment pp a;
      F.fprintf pp "@ ";
      pp_list_of_assignments pp r

let pp_assignments pp section = function
  | [] -> ()
  | l -> 
      F.fprintf pp "@[<v2>%s@,@[<v>" section;
      pp_list_of_assignments pp l;
      F.fprintf pp "@]@]@ "
	
let pp_invariant pp = function
  | None -> ()
  | Some(e) ->
      F.fprintf pp "@[<v2>INVARIANT@s%a@]@ " pp_expr e

let pp_guarded_command pp = function
  | Guarded(e, []) ->
      F.fprintf pp "  @[%a -->@]" pp_expr e
  | Default([]) ->
      F.fprintf pp "  ELSE -->"
  | Guarded(e, l) -> 
      F.fprintf pp "  @[<v3>%a -->@," pp_expr e;
      pp_list_of_assignments pp l;
      F.fprintf pp "@]"
  | Default(l) ->
      F.fprintf pp "  @[<v3>ELSE -->@,";
      pp_list_of_assignments pp l;
      F.fprintf pp "@]"

let pp_guarded_commands pp cmds = 
  let rec loop = function
    | [] -> ()
    | [cmd] -> pp_guarded_command pp cmd
    | cmd :: r ->
	pp_guarded_command pp cmd;
	F.fprintf pp "@ []@ ";
	loop r
  in
    F.fprintf pp "@[<v>";
    loop cmds;
    F.fprintf pp "@]"

let pp_transition pp = function
  | NoTransition -> ()   (* nothing to do *)
  | Assignments(l) -> pp_assignments pp "TRANSITION" l
  | GuardedCommands(l) ->
      F.fprintf pp "@[<v2>TRANSITION@ [@ ";
      pp_guarded_commands pp l;
      F.fprintf pp "@ ]@]@,"

let pp_module pp m = 
  F.fprintf pp "@[<v1>BEGIN@,";
  pp_state_var_decls pp m.state_vars;
  pp_assignments pp "INITIALIZATION" m.initialization;
  pp_assignments pp "DEFINITION" m.definition;
  pp_invariant pp m.invariant;
  pp_transition pp m.transition;
  F.fprintf pp "END@]"


(*
 * Full context
 *)
let pp_def pp = function    
  | Type_decl(x) ->
      F.fprintf pp "@[<h>%s:@ TYPE;@]@," x
  | Type_def(x, ty) ->
      F.fprintf pp "@[<h>%s:@ TYPE@ =@ %a;@]@,@\n" x pp_type ty
  | Constant_decl(x, ty) ->
      F.fprintf pp "@[<h>%s:@ %a;@]@,@\n" x pp_type ty
  | Constant_def(x, ty, v) -> 
      F.fprintf pp "@[<h>%s:@ %a@ =@ %a;@]@,@\n" x pp_type ty pp_expr v
  | Function_def(x, p, ty, v) ->
      pp_fun_def pp x p ty v;
      F.fprintf pp "@,@\n"
  | Assertion(x, tg, m, v) ->
      pp_assertion pp x tg m v;
      F.fprintf pp "@,@\n"
  | Module_def(x, m) -> 
      F.fprintf pp "@[<hov1>%s:@ MODULE@ =@,%a;@]@,@\n" x pp_module m

let pp_context pp ctx =
  F.fprintf pp "@[<hov2>%s: CONTEXT =@\n" ctx.ctx_name;
  F.fprintf pp "BEGIN@\n@[<v>";
  List.iter (fun def -> pp_def pp def) ctx.definitions;
  F.fprintf pp "@]END@]@."



(*
 * Pretty print using an output channel
 *)
let get_formatter ch =
  let pp = F.formatter_of_out_channel ch in
    F.pp_set_margin pp 120;
    pp

let print_type ch = pp_type (get_formatter ch)

let print_expr ch = pp_expr (get_formatter ch)

let print_module ch = pp_module (get_formatter ch)

let print_context ch = pp_context (get_formatter ch)
