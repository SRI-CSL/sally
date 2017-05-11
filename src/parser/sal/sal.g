/**
 * This file is part of sally.
 * Copyright (C) 2015 SRI International.
 *
 * Sally is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Sally is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with sally.  If not, see <http://www.gnu.org/licenses/>.
 */
grammar sal;

options {
  // C output for antlr
  language = 'C'; 
}
 
@parser::includes {
  #include <string>
  #include "command/command.h"
  #include "parser/sal/sal_state.h"
  using namespace sally;
}

@parser::postinclude {
  #define STATE (ctx->pState)
}


@parser::context
{
  /** The sally part of the parser state. */
  parser::sal_state* pState;
}

/** SAL context returned as a sequence command. */
command returns [cmd::command* cmd = 0]
  : context { cmd = STATE->finalize(); } 
  | EOF
  ; 

/** SAL context, with parameters for parametrization. */
context
@declarations {
  std::string name;
  parser::var_declarations_ctx parameters;
}
  : identifier[name] { STATE->new_context(name); }
    ('{' var_declaration_list[parameters] '}' { STATE->add_context_parameters(parameters); } ) ?  
    ':' KW_CONTEXT OP_EQ context_body
  ;

/** Body of the context */
context_body
  : KW_BEGIN declaration (';' declaration)* ';'? KW_END 
  ;

/** 
 * Individual declarations in the context. Usually, defined by defining a some 
 * constants (these are either instantiated to a value, or don't change during 
 * evolution), types, then the modules, and finally at least one property to 
 * check.  
 */
declaration 
  : constant_declaration
  | type_declaration     
  | module_declaration
  | assertion_declaration
  ;

/** Declaration of constants (including functions) */
constant_declaration
@declarations {
  std::string id;
  parser::var_declarations_ctx args;
  bool has_definition = false;
} 
  : identifier[id] ('(' var_declaration_list[args] ')')? ':' 
    t_type = type 
    { STATE->start_constant_declaration(id, args, t_type); }
    (OP_EQ t_definition = term)?
    { STATE->finish_constant_declaration(id, args, t_type, t_definition); }  
  ;

/** Declations of types */
type_declaration 
@declarations{
  std::string id;
}
  : identifier[id] ':' KW_TYPE OP_EQ t = type { STATE->define_type(id, t); }
  ;

/** Assertions (lemmas, theorems, ...) */
assertion_declaration
@declarations {
  std::string id;
} 
  : (identifier[id] ':')? form = assertion_form assertion_term[id, form]
  ;

/** Types of assertions (there is no semantics attached to these names) */
assertion_form returns [parser::sal::assertion_form form = parser::sal::SAL_LEMMA] 
  : KW_OBLIGATION { form = parser::sal::SAL_OBLIGATION; } 
  | KW_CLAIM { form = parser::sal::SAL_CLAIM; }
  | KW_LEMMA { form = parser::sal::SAL_LEMMA; }
  | KW_THEOREM { form = parser::sal::SAL_THEOREM; }
  ;

/** The actual assertion, does 'term' hold in the 'module' */
assertion_term[std::string id, parser::sal::assertion_form form]
  : m = module { STATE->push_scope(parser::SCOPE_ASSERTION); STATE->load_module_variables(m); }
    '|-' 
    t = term_or_g_term
    { STATE->pop_scope(parser::SCOPE_ASSERTION); }
    { STATE->add_assertion(id, form, m, t); }
  ;

term_or_g_term returns [expr::term_ref t]
  : 'G' '(' t1 = term ')' { t = t1; }
  | t2 = term { t = t2; }
  ; 

/** Definition of a module */
module_declaration 
@declarations{
  std::string id;
  parser::var_declarations_ctx args;
}
  : identifier[id]
    ('[' var_declaration_list[args] ']')?
    { STATE->start_module_declaration(args); } 
    ':' 'MODULE' OP_EQ m = module 
    { 
      STATE->finish_module_declaration(m, args);
      STATE->define_module(id, m); 
    }
  ;

/** Types */ 
type returns [expr::term_ref t]
@declarations{
  std::string id;
}
  : identifier[id] { t = STATE->get_type(id); }
  | t_builtin = builtin_type { t = t_builtin; }
  | t_scalar = scalar_type { t = t_scalar; STATE->register_enumeration(t); }
  | t_subrange = subrange_type { t = t_subrange; }
  | t_array = array_type { t = t_array; }
  | t_subtype = subtype { t = t_subtype; }
  | t_record = record_type { t = t_record; }
  ;

/** Built-in types */
builtin_type returns [expr::term_ref t]
  : KW_BOOLEAN { t = STATE->boolean_type(); }
  | KW_INTEGER { t = STATE->integer_type(); }
  | KW_NATURAL { t = STATE->natural_type(); }
  | KW_NZNAT   { t = STATE->nznat_type(); }
  | KW_REAL    { t = STATE->real_type(); }
  ;

/** Subtype of a type */
subtype returns [expr::term_ref t]
@declarations{
  std::string id;
}
  : '{' 
      identifier[id] ':' b = type '|' { STATE->start_predicate_subtype(id, b); } 
      p = term { t = STATE->finish_predicate_subtype(p); }  
    '}' 
  ;

/** List of scalars (an enum) */
scalar_type returns [expr::term_ref t]
@declarations{
  std::string id;
  std::vector<std::string> ids;
}
  : '{' 
      identifier[id] { ids.push_back(id); }
      (',' identifier[id] { ids.push_back(id); } )* 
    '}'
    { t = STATE->mk_enum_type(ids); }
  ;

/** Types that can be used for indexing */
index_type returns [expr::term_ref t]
@declarations{
  std::string id;
}
  : t1 = type { t = t1; STATE->check_index_type(t); }
  ;

/** Bound is either a term or infinity */
bound returns [expr::term_ref t]
  : t1 = term { t = t1; } 
  | '_'
  ;

/** Range types */
subrange_type returns [expr::term_ref t] 
  : '[' b1 = bound '..' b2 = bound ']' { t = STATE->mk_subrange_type(b1, b2); }
  ;

/** Array type, from indices to elements */
array_type returns [expr::term_ref t]
  : KW_ARRAY it = index_type KW_OF et = type { t = STATE->mk_array_type(it, et); }
  ;

/** Record types */
record_type returns [expr::term_ref t]
@declarations{
  parser::var_declarations_ctx record_elements;
}
  : '[#' var_declaration_list[record_elements] '#]' { t = STATE->mk_record_type(record_elements); }
  ;

// Expressions: typical

term returns [expr::term_ref t]
  : t1 = quantified_term { t = t1; }
  ; 
  
quantified_term returns [expr::term_ref t] 
@declarations{
  parser::var_declarations_ctx bindings;
}
  : KW_FORALL '(' var_declaration_list[bindings] ')' ':' { STATE->start_quantifier(bindings); } 
    t_forall = term { t = STATE->finish_quantifier(expr::TERM_FORALL, t_forall); }
  | KW_EXISTS '(' var_declaration_list[bindings] ')' ':' { STATE->start_quantifier(bindings); }
    t_exists = term { t = STATE->finish_quantifier(expr::TERM_EXISTS, t_exists); }
  | t1 = update_term { t = t1; }
  ;

update_term returns [expr::term_ref t]
@declarations{
  std::vector<expr::term_ref> accessors;
}
  : t1 = iff_term { t = t1; }
    (
      { accessors.clear(); }
      KW_WITH 
        (t2 = term_access { accessors.push_back(t2); })+ 
      ':=' 
        t3 = iff_term 
      { t = STATE->mk_term_update(t, accessors, t3); } 
    )*
  ;

    
iff_term returns [expr::term_ref t]
  : t1 = implies_term { t = t1; }  
    (OP_IFF t2 = implies_term { t = STATE->mk_term(expr::TERM_EQ, t, t2); } )?
  ;

implies_term returns [expr::term_ref t]
  : t1 = or_term { t = t1; }
    (OP_IMPLIES t2 = or_term { t = STATE->mk_term(expr::TERM_IMPLIES, t, t2); } )?
  ;

or_term returns [expr::term_ref t]
  : t1 = and_term { t = t1; } 
    (KW_OR t2 = and_term { t = STATE->mk_term(expr::TERM_OR, t, t2); } )*
  ; 
  
and_term returns [expr::term_ref t]
  : t1 = xor_term { t = t1; }
    (KW_AND t2 = xor_term { t = STATE->mk_term(expr::TERM_AND, t, t2); } )*
  ;

xor_term returns [expr::term_ref t]
  : t1 = unary_bool_term { t = t1; }  
    (KW_XOR t2 = unary_bool_term { t = STATE->mk_term(expr::TERM_XOR, t, t2); } )*    
  ;

unary_bool_term returns [expr::term_ref t]
  : NOT t_not = unary_bool_term { t = STATE->mk_term(expr::TERM_NOT, t_not); }
  | t_eq = eq_term { t = t_eq; }
  ;

boolean_constant_term returns [expr::term_ref t]
  : KW_TRUE { t = STATE->mk_boolean_constant(true); }
  | KW_FALSE { t = STATE->mk_boolean_constant(false); }
  ;
  
eq_term returns [expr::term_ref t]
@declarations{
  bool negated = false;
}  
  : t1 = rel_term { t = t1; }
    ( 
      ( OP_EQ 
      | OP_NEQ { negated = true; }
      ) 
      t2 = rel_term { 
        t = STATE->mk_term(expr::TERM_EQ, t, t2);
        if (negated) { t = STATE->mk_term(expr::TERM_NOT, t); }  
      } 
    )?
  ;

rel_term returns [expr::term_ref t] 
@declarations{
  expr::term_op op = expr::OP_LAST;
}  
  : t1 = additive_term { t = t1; } 
    (
      ( OP_GT  { op = expr::TERM_GT; }  
      | OP_GEQ { op = expr::TERM_GEQ; } 
      | OP_LT  { op = expr::TERM_LT; }
      | OP_LEQ { op = expr::TERM_LEQ; }
      ) t2 = additive_term
    )?
    { if (op != expr::OP_LAST) t = STATE->mk_term(op, t, t2); }
  ;

/** Associative reading, evaluate from left to right. */
additive_term returns [expr::term_ref t] 
@declarations{
  expr::term_op op;
} 
  : t1 = multiplicative_term { t = t1; } 
    (
      ( OP_ADD { op = expr::TERM_ADD; } 
      | OP_SUB { op = expr::TERM_SUB; }
      ) 
      t2 = multiplicative_term { t = STATE->mk_term(op, t, t2); } 
    )*
  ;

/** Associative reading, evaluate from left to right. */
multiplicative_term returns [expr::term_ref t] 
@declarations{
  expr::term_op op;
}
  : t1 = unary_nonformula_term { t = t1; } 
    (
      ( OP_MUL { op = expr::TERM_MUL; } 
      | OP_DIV { op = expr::TERM_DIV; }
      | KW_MOD { op = expr::TERM_MOD; }
      | KW_DIV { op = expr::TERM_DIV; }
      ) 
      t2 = unary_nonformula_term { t = STATE->mk_term(op, t, t2); } 
    )*
  ;

unary_nonformula_term returns [expr::term_ref t]
  : OP_SUB t_sub = unary_nonformula_term { t = STATE->mk_term(expr::TERM_SUB, t_sub); } 
  | t_base = base_term { t = t_base; }
  ;

/** 
 * Base term is a non-breakable unit with potential let declaration ahead of it.
 */
base_term returns [expr::term_ref t]
  : KW_LET { STATE->push_scope(parser::SCOPE_LET); } 
      let_declarations 
    KW_IN 
      t_let = base_term { STATE->pop_scope(parser::SCOPE_LET); t = t_let; }
  | t_prefix = base_term_prefix { t = t_prefix; }  
    (t_with_suffix = base_term_suffix[t_prefix] { t_prefix = t_with_suffix; } )* { t = t_prefix; }
  ;

base_term_prefix returns [expr::term_ref t] 
@declarations{
  std::string id;
  std::vector<expr::term_ref> terms;
  bool next = false;
  parser::var_declarations_ctx var_ctx;
  expr::term_manager::id_to_term_map rec_map;
} 
  : identifier[id] ('\'' { next = true; })? { t = STATE->get_variable(id, next); }
  | r = rational_constant { t = STATE->mk_rational_constant(r); }
  | b = boolean_constant_term { t = b; } 
  | '[' '[' index_var_declaration[var_ctx] ']' { STATE->start_indexed_array(var_ctx); }
        t_array = term 
    ']' { t = STATE->finish_indexed_array(t_array); }
  | '(#' record_entry[rec_map] (',' record_entry[rec_map])* '#)' { t = STATE->mk_record(rec_map); } 
  | '(' term_list[terms] ')' { t = (terms.size() == 1) ? terms[0] : STATE->mk_tuple(terms); } 
  | t_cond = conditional_term { t = t_cond; }
  ;

conditional_term returns [expr::term_ref t]
@declarations{
  std::vector<expr::term_ref> ite_terms;
}
  : KW_IF   t_cond = term { ite_terms.push_back(t_cond); }
    KW_THEN t_then = term { ite_terms.push_back(t_then); }
    (
     KW_ELSIF t_else1 = term { ite_terms.push_back(t_else1); } 
     KW_THEN t_else2 = term { ite_terms.push_back(t_else2); }
    )* 
    KW_ELSE t_else = term { ite_terms.push_back(t_else); }
    KW_ENDIF
    { t = STATE->mk_ite(ite_terms); }
  ;

base_term_suffix[expr::term_ref prefix] returns [expr::term_ref t]
@declarations{
  std::vector<expr::term_ref> args;
}
  : term_argument[args] { t = STATE->mk_fun_app(prefix, args); }
  | t1 = term_access { t = STATE->mk_term_access(prefix, t1); } 
  ;

let_declarations 
  : let_declaration (',' let_declaration)*
  ;

let_declaration
@declarations{
  std::string id;
} 
  : identifier[id] 
    (':' t_type = type )? 
    OP_EQ 
    t_term = term { STATE->define_var_in_scope(id, t_type, t_term); }
  ;

record_entry[expr::term_manager::id_to_term_map& str_term_map] 
@declarations{
  std::string id;
}
  : identifier[id] ':=' t = term { STATE->add_to_map(str_term_map, id, t); }
  ;

set_term[expr::term_ref in_arg] returns [expr::term_ref t]
@declarations{
  std::string id;
  std::vector<expr::term_ref> set_elements;
}
  : '{' 
        identifier[id] ':' t1 = type '|' { STATE->start_set_abstraction(in_arg, id, t1); }
        t2 = term 
    '}' { t = t2; STATE->end_set_abstraction(); }
  | '{' (
        t3 = term { set_elements.push_back(t3); }
        (',' t4 = term { set_elements.push_back(t4); } )*
        )? 
    '}' { t = STATE->mk_set_enumeration(in_arg, set_elements); }
  ;

term_argument[std::vector<expr::term_ref>& terms]
  : '(' term_list[terms] ')' 
  ;

term_list[std::vector<expr::term_ref>& terms] 
  : t1 = term { terms.push_back(t1); } 
    (',' t2 = term { terms.push_back(t2); } )* 
  ;

index_var_declaration[parser::var_declarations_ctx& var_ctx]
@declarations{
  std::string id;
} 
  : identifier[id] ':' t = index_type { var_ctx.add(id, t); }
  ;

identifier_list[parser::var_declarations_ctx& var_ctx]
@declarations{
  std::string id;
}
  : identifier[id] { var_ctx.add(id); }  
    (',' identifier[id] { var_ctx.add(id); } )* 
  ;

pidentifier_list[parser::var_declarations_ctx& var_ctx]
  : identifier_list[var_ctx];

var_declaration[parser::var_declarations_ctx& var_ctx] 
  : identifier_list[var_ctx] ':' t = type { var_ctx.add(t); } 
  ;

var_declaration_list[parser::var_declarations_ctx& var_ctx] 
  : var_declaration[var_ctx] (',' var_declaration[var_ctx])*
  ;

/* The Transition Language */

lvalue returns [expr::term_ref t] 
@declarations{
  std::string id;
  bool next = false;
  std::vector<expr::term_ref> accessors; 
}
  : identifier[id] ('\'' { next = true; })? 
    { t = STATE->get_variable(id, next); }
    ( t1 = term_access { accessors.push_back(t1); })*
    { t = STATE->mk_term_access(t, accessors); }
  ;

term_access returns [expr::term_ref t]
@declarations{
  std::string id;
}
  : '[' i = term ']'   { t = i; }
  | '.' identifier[id] { t = STATE->mk_string(id); }
  ;

rhs_definition[expr::term_ref lhs] returns [expr::term_ref t] 
  : OP_EQ 
      rhs = term { t = STATE->mk_assignment(lhs, rhs); }  
  | KW_IN { STATE->ensure_variable(lhs, STATE->in_transition()); } 
      t1 = set_term[lhs] { t = t1; } 
  ;

simple_definition returns [expr::term_ref t] 
  : t1 = lvalue { STATE->lvalues_add(t1 ); } 
    t2 = rhs_definition[t1] { t = t2; }
  ;

forall_definition returns [expr::term_ref t] 
@declarations{
  parser::var_declarations_ctx var_ctx;
}
  : '(' KW_FORALL 
      '(' var_declaration_list[var_ctx] { STATE->start_quantifier(var_ctx); } ')' 
        ':' body = definition_list 
    ')' 
    { t = STATE->finish_quantifier(expr::TERM_FORALL, body); }
  ;

/**
 * Definitions are the basic constructs used to build up the invariants, 
 * initializations, and transitions of a module. Definitions are used to specify 
 * the trajectory of variables in a computation by providing constraints on the 
 * controlled variables in a transition system. For variables ranging over 
 * aggregate data structures like records or arrays, it is possible to define 
 * each component separately. For example,
 *   
 *  x’ = x + 1
 * 
 * simply increments the state variable x, where x’ is the newstate of the 
 * variable,
 *  
 *  y’[i] = 3
 * 
 * sets the new state of the array y to be 3 at index i, and to remain unchanged
 * on all other indices, and
 *
 *  z.foo.1[0] = y
 * 
 * constrains state variable z, which is a record whose foo component is a 
 * tuple, whose first component in turn is an array of the same type as y.
 */
definition returns [expr::term_ref t]
  : t_simple = simple_definition { t = t_simple; STATE->check_term(t_simple); } 
  | t_forall = forall_definition { t = t_forall; STATE->check_term(t_forall); } 
  ;

/** Definitions return a conjunction of definitions (or a single definition) */
definition_list returns [expr::term_ref t]
  : { STATE->lvalues_clear(); }
    t1 = definition { t = t1; } 
    (';' t2 = definition { STATE->mk_term(expr::TERM_AND, t, t2); })* 
    ';'?
    { STATE->lvalues_clear(); }
  ;

assignments[std::vector<expr::term_ref>& a]
  : { STATE->lvalues_clear(); }
    t1 = simple_definition { a.push_back(t1); } 
    (';' t2 = simple_definition { a.push_back(t2); })* ';'?
    { STATE->lvalues_clear(); }
  ;

/** 
 * Each guarded command consists of a guard formula and an assignment part. The 
 * guard is a boolean expression in the current controlled (local, global, and 
 * output) variables and current and next state input variables. The assignment 
 * part is a list of equalities between a left-hand side next state variable and 
 * a right-hand side expression in current and next state variables.
 */
guarded_command returns [expr::term_ref t] 
@declarations{
  std::vector<expr::term_ref> a;
}
  : guard = term { STATE->guards_add(guard); } 
    '-->' assignments[a]? { t = STATE->mk_term_from_guarded(guard, a); STATE->check_term(t); }  
  ;

guarded_else_command returns [expr::term_ref t]
@declarations{
  std::vector<expr::term_ref> a;
}
  : KW_ELSE '-->' assignments[a]? 
    { t = STATE->mk_term_from_guarded(expr::term_ref(), a); STATE->check_term(t); }
  ;

/* The Module Language */

/** 
 * A module is a self-contained specification of a transition system in SAL. 
 * Modules can be independently analyzed for properties and composed 
 * synchronously or asynchronously.
 */
module returns [parser::sal::module::ref m]
  : m1 = unary_module_modifier { m = m1; } 
  ;  
 
/** Prefix module operations */
unary_module_modifier returns [parser::sal::module::ref m]
@declarations{
  parser::var_declarations_ctx var_ctx;
  parser::sal::module::id_to_lvalue subst_map;
}
  : // Synchronous composition 
    { m = STATE->start_module(); }
    OP_SYNC '(' index_var_declaration[var_ctx] ')' ':' 
    { STATE->start_indexed_composition(var_ctx); }
    m_sync = unary_module_modifier
    { STATE->finish_indexed_composition(m_sync, m, parser::sal::SAL_COMPOSE_SYNCHRONOUS); }
    { STATE->finish_module(m); }
    
  | // Asynchronous composition 
    { m = STATE->start_module(); }
    OP_ASYNC '(' index_var_declaration[var_ctx] ')' ':'
    { STATE->start_indexed_composition(var_ctx); } 
    m_async = unary_module_modifier
    { STATE->finish_indexed_composition(m_sync, m, parser::sal::SAL_COMPOSE_SYNCHRONOUS); }
    { STATE->finish_module(m); }
    
  | // Make listed variables *local* 
    { m = STATE->start_module(); }
    KW_LOCAL pidentifier_list[var_ctx] KW_IN m_local = unary_module_modifier
    { STATE->module_modify_local(m, m_local, var_ctx); }
    { STATE->finish_module(m); }
      
  | // Make listed variables *output*
    { m = STATE->start_module(); }
    KW_OUTPUT pidentifier_list[var_ctx] KW_IN m_output = unary_module_modifier
    { STATE->module_modify_output(m, m_output, var_ctx); }
    { STATE->finish_module(m); }
      
  | // Make a module while renaming some variables 
    { m = STATE->start_module(); }
    KW_RENAME rename_list[subst_map] KW_IN m_rename = unary_module_modifier
    { STATE->module_modify_rename(m, m_rename, subst_map); }
    { STATE->finish_module(m); }
    
  | // Module *with* some new variables
    { m = STATE->start_module(); } 
    KW_WITH new_var_declaration_list[m] m_with = unary_module_modifier
    { STATE->module_modify_with(m, m_with); }
    { STATE->finish_module(m); }
            
  | m_base = synchronous_module_composition { m = m_base; }
  ;

/**
 * The semantics of synchronous composition is that the module M1 || M2 
 * consists of:
 * - The initializations are the combination of initializations.
 * - The transitions are the combination of the individual transitions.
 * - The definitions are the union of the definition.
 * - The initializations are the pairwise combination of the initializations. 
 * - Two guarded initializations are combined by conjoining the guards and by 
 *   taking the union of the assignments. 
 */
synchronous_module_composition returns [parser::sal::module::ref m]
  : m1 = asynchronous_module_composition { m = m1; }
    (OP_SYNC m2 = asynchronous_module_composition { m = STATE->composition(m, m2, parser::sal::SAL_COMPOSE_SYNCHRONOUS); } )*
  ;  

/**
 * The semantics of asynchronous composition of two modules is given by the 
 * conjunction of the initializations, and the interleaving of the transitions 
 * of the two modules.
 */
asynchronous_module_composition returns [parser::sal::module::ref m]
  : m1 = module_base { m = m1; } 
    (OP_ASYNC m2 = module_base { m = STATE->composition(m, m2, parser::sal::SAL_COMPOSE_ASYNCHRONOUS); } )*
  ; 


/** The base of the module expressions */
module_base returns [parser::sal::module::ref m]
  : m_ref = module_name { m = m_ref; }
  | m_base = base_module { m = m_base; }
  | ('(' m_bracket = module ')') { m = m_bracket; }
  ;

/**
 * A BaseModule identifies the pairwise distinct sets of input, output, global, 
 * and local variables. This characterizes the state of the module. Base modules 
 * also may consist of several sections that can be given in any order. There 
 * may, for example, be 3 distinct TRANSITION sections. In every case, it is the 
 * same as if there was a prescribed order, with each class of variable and 
 * section being the union of the individual declarations.
 */
base_module returns [parser::sal::module::ref m]
  : { m = STATE->start_module(); }
    KW_BEGIN base_declaration_list[m] KW_END
    { STATE->finish_module(m); }
  ;

base_declaration_list[parser::sal::module::ref m]
  : base_declaration[m]* 
  ;

base_declaration[parser::sal::module::ref m]
@declarations{
  parser::var_declarations_ctx vars_ctx;
}
  : input_declaration[vars_ctx] { STATE->declare_variables(m, parser::sal::SAL_VARIABLE_INPUT, vars_ctx); }
  | output_declaration[vars_ctx] { STATE->declare_variables(m, parser::sal::SAL_VARIABLE_OUTPUT, vars_ctx); }
  | global_declaration[vars_ctx] { STATE->declare_variables(m, parser::sal::SAL_VARIABLE_GLOBAL, vars_ctx); }
  | local_declaration[vars_ctx] { STATE->declare_variables(m, parser::sal::SAL_VARIABLE_LOCAL, vars_ctx); }
  | definition_declaration[m] 
// DJ: removed, not in manual  | invariant_declaration[m] 
// DJ: removed, not in manual  | init_formula_declaration[m] 
  | initialization_declaration[m]
  | transition_declaration[m]
  ;

rename_list[parser::sal::module::id_to_lvalue& m] 
  : rename[m] (',' rename[m])*
  ;

rename [parser::sal::module::id_to_lvalue& m]
@declarations{
  std::string id;
}
  : identifier[id] KW_TO t2 = lvalue { STATE->add_to_renaming_map(m, id, t2); } 
  ;

module_name returns [parser::sal::module::ref m]
@declarations{
  std::string id;
  std::vector<expr::term_ref> args;
}
  : identifier[id] module_actuals[args] { m = STATE->get_module(id, args); }
  ;

module_actuals[std::vector<expr::term_ref>& args] 
  : ('[' term_list[args] ']')?
  ;

/* Declarations within modules */

/**
 * From the SAL manual:
 * 
 * The state type is defined by four pairwise disjoint sets of input, output, 
 * global, and local variables. The input and global variables are the observed 
 * variables of a module and the output, global, and local variables are the 
 * controlled variables of the module.
 *
 * TODO: Can the module change global variables?
 */


input_declaration[parser::var_declarations_ctx& var_ctx] 
  : KW_INPUT var_declaration_list[var_ctx]
  ;

output_declaration[parser::var_declarations_ctx& var_ctx] 
  : KW_OUTPUT var_declaration_list[var_ctx]
  ;

global_declaration[parser::var_declarations_ctx& var_ctx] 
  : KW_GLOBAL var_declaration_list[var_ctx]
  ;

local_declaration[parser::var_declarations_ctx& var_ctx]
  : KW_LOCAL var_declaration_list[var_ctx]
  ;

/**
 * Definitions appearing in the DEFINITION section(s) are treated as invariants
 * for the system. When composed with other modules, the definitions remain true
 * even during the transitions of the other modules. This section is usually 
 * used to define controlled variables whose values ultimately depend on the 
 * inputs, for example, a boolean variable that becomes true when the 
 * temperature goes above a specified value.
 */
definition_declaration[parser::sal::module::ref m]
  : KW_DEFINITION { STATE->start_definition(); }
      t = definition_list { STATE->add_definition(m, t); }
    { STATE->end_definition(); }
  ;

/**
 * The INITIALIZATION section(s) constrain the possible initial values for the 
 * local, global, and output declarations. Input variables may not be 
 * initialized. The INITIALIZATION section(s) determine a state predicate that 
 * holds of the initial state of the base module. Definitions and guarded 
 * commands appearing in the INITIALIZATION section must not contain any 
 * NextVariable occurrences, i.e., both sides of the defining equation must be 
 * current expressions.
 * 
 * Guards may refer to any variables, this acts as a form of postcondition when
 * controlled variables are involved. This is like backtracking: operationally a 
 * guarded initialization is selected, the assignments made, and if the 
 * assignments violate the guard the assignments are undone and a new guarded 
 * initialization is selected. 
 */
initialization_declaration[parser::sal::module::ref m]
  : KW_INITIALIZATION { STATE->start_initialization(); }
      t1 = definition_or_command { STATE->add_initialization(m, t1); }  
      (';' t2 = definition_or_command { STATE->add_initialization(m, t2); } )* 
      ';'?
    { STATE->end_initialization(); }
  ;

/**
 * The TRANSITION section(s) constrain the possible next states for the local,
 * global, and output declarations. As this is generally defined relative to the
 * previous state of the module, the transition section(s) determine a state 
 * relation. Input variables may not appear on the Lhs of any assignments. 
 * Guards may refer to any variables, even NextVariables. As with guarded 
 * initial transitions, guards involving NextVariables have to be evaluated 
 * after the assignments have been made, and if they are false the assignments 
 * must be undone and a new guarded transition selected.
 */
transition_declaration[parser::sal::module::ref m]
  : KW_TRANSITION { STATE->start_transition(); }
      t1 = definition_or_command { STATE->add_transition(m, t1); }
      (';' t2 = definition_or_command { STATE->add_transition(m, t2); })* 
      ';'?
    { STATE->end_transition(); }
  ; 
 
// DJ: removed, not in manual
// invariant_declaration[parser::sal::module::ref m]
//  : KW_INVARIANT t = term { STATE->add_invariant(m, t); }
//  ;

// DJ: removed, not in manual
// init_formula_declaration[parser::sal::module::ref m]
//  : KW_INITFORMULA t = term { STATE->add_init_formula(m, t); }
// ;

multi_command returns [expr::term_ref t]
@declarations{
  parser::var_declarations_ctx arg_ctx;
} 
  : '(' OP_ASYNC
        { STATE->start_multi_command(); } 
        '(' var_declaration_list[arg_ctx] ')' 
        { STATE->start_quantifier(arg_ctx); }
        ':' body = some_command 
        { STATE->end_multi_command(); } 
        { t = STATE->finish_quantifier(expr::TERM_EXISTS, body); }
    ')' 
  ;

some_command returns [expr::term_ref t] 
@declarations{
  std::string id;
}
  : (identifier[id] ':') ? t_guarded = guarded_command { t = t_guarded; STATE->check_term(t); } 
  | (identifier[id] ':') ? t_multi = multi_command { t = t_multi; STATE->check_term(t); } 
  ;

some_commands returns [expr::term_ref t]
@declarations{
  std::vector<expr::term_ref> cmds;
  bool has_else = false;  
}
  : { STATE->guards_clear(); } 
    t1 = some_command { cmds.push_back(t1); STATE->check_term(t1); } 
    (OP_ASYNC t2 = some_command { cmds.push_back(t2); STATE->check_term(t2); })*
    (OP_ASYNC te = guarded_else_command { cmds.push_back(te); STATE->check_term(te); has_else = true; } )?
    { t = STATE->mk_term_from_commands(cmds, has_else); }
    { STATE->guards_clear(); }
  ;

definition_or_command returns [expr::term_ref t]
  : t_def = definition { t = t_def; }
  | ('[' t_cmds = some_commands ']') { t = t_cmds; } 
  ;

/** Declare new variables in the given module */
new_var_declaration[parser::sal::module::ref m]
@declarations{
  parser::var_declarations_ctx vars_ctx;
} 
  : input_declaration[vars_ctx] { STATE->declare_variables(m, parser::sal::SAL_VARIABLE_INPUT, vars_ctx); }
  | output_declaration[vars_ctx] { STATE->declare_variables(m, parser::sal::SAL_VARIABLE_OUTPUT, vars_ctx); }
  | global_declaration[vars_ctx] { STATE->declare_variables(m, parser::sal::SAL_VARIABLE_GLOBAL, vars_ctx); }
  ;

new_var_declaration_list[parser::sal::module::ref m] 
  : new_var_declaration[m] (';' new_var_declaration[m])*
  ;

identifier[std::string& id] 
  : IDENTIFIER { id = STATE->token_text($IDENTIFIER); }
  ;

rational_constant returns [expr::rational rat]
  : n1 = NUMERAL ('.' n2 = NUMERAL )? { rat = STATE->mk_rational(n1, n2); }
  ;

/** Numerals */
NUMERAL: DIGIT+;

/** Keywords */ 
KW_ARRAY: A R R A Y; 
KW_BEGIN: B E G I N;
KW_CONTEXT: C O N T E X T;
KW_CLAIM: C L A I M;
KW_DEFINITION: D E F I N I T I O N;
KW_DIV: D I V;
KW_ELSIF: E L S I F;
KW_ELSE: E L S E;
KW_ENDIF: E N D I F;
KW_END: E N D;
KW_EXISTS: E X I S T S;
KW_FORALL: F O R A L L;
KW_GLOBAL: G L O B A L;
// DJ: removed, not in manual KW_INITFORMULA: I N I T F O R M U L A;
KW_INITIALIZATION: I N I T I A L I Z A T I O N;
// DJ: removed, not in manual KW_INVARIANT: I N V A R I A N T;
KW_INPUT: I N P U T; // Had to rename because it clashes with antlr #define INPUT
KW_IF: I F;
KW_IN: I N;
KW_LET: L E T;
KW_LEMMA: L E M M A;
KW_LOCAL: L O C A L;
KW_MOD: M O D;
KW_OF: O F;
KW_OUTPUT: O U T P U T;
KW_OBLIGATION: O B L I G A T I O N;
KW_OBSERVE: O B S E R V E;
KW_RENAME: R E N A M E;
KW_THEN: T H E N;
KW_THEOREM: T H E O R E M;
KW_TRANSITION: T R A N S I T I O N;
KW_TYPE: T Y P E;
KW_TO: T O;
KW_WITH: W I T H;

/** Types */
KW_BOOLEAN: B O O L (E A N)?;
KW_INTEGER: I N T E G E R;
KW_NATURAL: N A T (U R A L)?;
KW_NZNAT: N Z N A T;
KW_REAL: R E A L;

/** Boolean opearators */
KW_TRUE: T R U E;
KW_FALSE: F A L S E;
KW_AND: A N D;
KW_OR: O R;
KW_XOR: X O R;
NOT: N O T;
OP_IMPLIES: '=>';
OP_IFF: '<=>';

// Arithmetic Operators
OP_SUB: '-';
OP_ADD: '+';
OP_MUL: '*';
OP_DIV: '/';

// Relational Operators
OP_LEQ: '<=';
OP_LT: '<';
OP_GEQ: '>=';
OP_GT: '>';
OP_NEQ: '/=';
OP_EQ: '=';

// Combination operators
OP_SYNC: '||' ;
OP_ASYNC: '[]';

/** Letters */ 
fragment                                     
LETTER : 'a'..'z' | 'A'..'Z';

/** Digits */
fragment   
DIGIT : '0'..'9';

/** Whitespace characters */
fragment
WHITESPACE : ' ' | '\t' | '\n' | '\r' | '\f';

/** Comments (which we skip) */
SL_COMMENT
  : '%' (~('\n'|'\r'))* ('\n'|'\r'('\n')?) { SKIP(); }
  ;

/** Whitespace (skip) */
WHITESPACE_SKIP
  : WHITESPACE+ { SKIP(); }
  ;
   
/** Identifiers */
IDENTIFIER
  : LETTER (LETTER | DIGIT | '?' | '_' )*
  ;

/** Case insensitive matches */
fragment A:('a'|'A');
fragment B:('b'|'B');
fragment C:('c'|'C');
fragment D:('d'|'D');
fragment E:('e'|'E');
fragment F:('f'|'F');
fragment G:('g'|'G');
fragment H:('h'|'H');
fragment I:('i'|'I');
fragment J:('j'|'J');
fragment K:('k'|'K');
fragment L:('l'|'L');
fragment M:('m'|'M');
fragment N:('n'|'N');
fragment O:('o'|'O');
fragment P:('p'|'P');
fragment Q:('q'|'Q');
fragment R:('r'|'R');
fragment S:('s'|'S');
fragment T:('t'|'T');
fragment U:('u'|'U');
fragment V:('v'|'V');
fragment W:('w'|'W');
fragment X:('x'|'X');
fragment Y:('y'|'Y');
fragment Z:('z'|'Z');  
  