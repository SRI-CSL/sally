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

#include "parser/sal/sal_state.h"
#include "parser/parser.h"
#include "command/command.h"

#include "expr/term_manager.h"
#include "expr/gc_relocator.h"

#include "utils/trace.h"

#include <cassert>
#include <iostream>

using namespace sally;
using namespace parser;
using namespace expr;

using namespace std;

void var_declarations_ctx::add(std::string name, term_ref type) {
  var_names.push_back(name);
  var_types.push_back(type);
  assert(var_names.size() == var_types.size());
}

void var_declarations_ctx::add(std::string name) {
  assert(var_names.size() >= var_types.size());
  var_names.push_back(name);
}

void var_declarations_ctx::add(term_ref type) {
  assert(var_names.size() > var_types.size());
  while (var_names.size() > var_types.size()) {
    var_types.push_back(type);
  }
}

sal_state::sal_state(const system::context& context)
: d_context(context)
, d_sal_context(0)
, d_variables("local vars")
, d_types("types")
, d_modules("modules")
, d_in_transition(false)
, d_multi_commands(0)
{
  // Add the basic types
  term_manager& tm = context.tm();
  d_boolean_type = tm.boolean_type();
  d_integer_type = tm.integer_type();
  d_x = tm.mk_variable("x", d_integer_type);
  term_ref zero = tm.mk_rational_constant(rational(0, 1));
  d_natural_type = tm.mk_predicate_subtype(d_x, tm.mk_term(TERM_GEQ, d_x, zero));
  d_nznat_type = tm.mk_predicate_subtype(d_x, tm.mk_term(TERM_GT, d_x, zero));
  d_real_type = tm.real_type();
}

string sal_state::token_text(pANTLR3_COMMON_TOKEN token) {
  ANTLR3_MARKER start = token->getStartIndex(token);
  size_t size = token->getStopIndex(token) - start + 1;
  return string((const char*) start, size);
}

term_ref sal_state::get_type(std::string id) const {
  if (!d_types.has_entry(id)) {
    throw parser_exception(id + " undeclared");
  }
  return d_types.get_entry(id);
}

term_ref sal_state::new_variable(std::string name, term_ref type, bool has_next) {
  term_ref var = tm().mk_variable(name, type);
  if (has_next) {
    term_ref var_next = tm().mk_variable(name + "'", type);
    assert(d_var_to_next_map.find(var) == d_var_to_next_map.end());
    d_var_to_next_map[var] = var_next;
    d_next_to_var_map[var_next] = var;
  }
  return var;
}

bool sal_state::is_variable(std::string id, bool next) const {
  if (!d_variables.has_entry(id)) {
    return false;
  }
  if (next) {
    // Check for next version
    term_ref var = d_variables.get_entry(id);
    return d_var_to_next_map.find(var) != d_var_to_next_map.end();
  } else {
    return true;
  }
}

term_ref sal_state::get_variable(std::string id, bool next) const {
  if (!d_variables.has_entry(id)) {
    throw parser_exception(id + " undeclared");
  }
  term_ref var = d_variables.get_entry(id);
  if (next) {
    term_to_term_map::const_iterator find = d_var_to_next_map.find(var);
    assert(find != d_var_to_next_map.end());
    var = find->second;
  }
  return var;
}

void sal_state::ensure_variable(term_ref x, bool next) const {
  
  term_ref x_next = x;

  // Must be a variable
  const term& x_term = tm().term_of(x);
  if (x_term.op() != VARIABLE) {
    throw parser_exception(tm()) << "Expecting a variable, got " << x << ".";
  }

  // Check the right version 
  if (next) {
    x = get_state_variable(x_next);
  } else {
    x_next = get_next_state_variable(x);
  }

  // Get the module and make sure variable is in state
  assert(d_current_module.size() > 0);
  sal::module::ref m = d_current_module.back();
  m->get_variable_class(x);
}

bool sal_state::has_next_state(expr::term_ref var) const {
  return d_var_to_next_map.find(var) != d_var_to_next_map.end();
}


term_ref sal_state::get_next_state_variable(term_ref var) const {
  term_to_term_map::const_iterator find = d_var_to_next_map.find(var);
  if (find == d_var_to_next_map.end()) {
    throw parser_exception(tm()) << "term " << var << " is not a state variable";
  }
  return find->second;
}

term_ref sal_state::get_state_variable(term_ref next_var) const {
  term_to_term_map::const_iterator find = d_next_to_var_map.find(next_var);
  if (find == d_next_to_var_map.end()) {
    throw parser_exception(tm()) << "term " << next_var << " is not a next-state variable";
  }
  return find->second;
}

term_ref sal_state::get_next_state_term(expr::term_ref term) const {
  // Get variables, and substitute with next versions if any
  std::vector<term_ref> term_vars;
  tm().get_variables(term, term_vars);
  expr::term_manager::substitution_map subst;
  for (size_t i = 0; i < term_vars.size(); ++ i) {
    term_ref x = term_vars[i];
    if (has_next_state(x)) {
      term_ref x_next = get_next_state_variable(x);
      subst[x] = x_next;
    }
  }
  return tm().substitute(term, subst);
}

sal::module::ref sal_state::get_module(std::string name, const std::vector<term_ref>& actuals) {
  if (!d_modules.has_entry(name)) {
    throw parser_exception(name + " undeclared");
  }
  sal::module::ref m = d_modules.get_entry(name);
  if (actuals.size() > 0) {
    m = m->instantiate(actuals);
  }
  return m;
}

void sal_state::push_scope(scope_type type) {
  d_variables.push_scope();
  d_types.push_scope();
  d_scope.push_back(type);
}

void sal_state::pop_scope(scope_type type) {
  d_variables.pop_scope();
  d_types.pop_scope();
  assert(d_scope.back() == type);
  d_scope.pop_back();
}

void sal_state::gc_collect(const gc_relocator& gc_reloc) {
  d_variables.gc_relocate(gc_reloc);
  d_types.gc_relocate(gc_reloc);
}

cmd::command* sal_state::finalize() {
  return d_sal_context->to_sally_commands(d_context);
}

rational sal_state::mk_integer(pANTLR3_COMMON_TOKEN token) {
  return rational(token_text(token));
}

rational sal_state::mk_rational(pANTLR3_COMMON_TOKEN token1, pANTLR3_COMMON_TOKEN token2) {
  if (token2) {
    std::string decimals = token_text(token2);
    std::stringstream ss;
    ss << token_text(token1) << decimals;
    integer numerator = integer(ss.str(), 10);
    integer denominator = integer(10).pow(decimals.size());
    return rational(numerator, denominator);
  } else {
    return rational(token_text(token1));
  }
}

term_ref sal_state::mk_rational_constant(const rational& rat) {
  return tm().mk_rational_constant(rat);
}

term_ref sal_state::mk_boolean_constant(bool value) {
  return tm().mk_boolean_constant(value);
}

term_ref sal_state::mk_string(std::string s) {
  return tm().mk_string_constant(s);
}

void sal_state::new_context(std::string name) {
  assert(d_sal_context == 0);
  d_sal_context = new sal::context(tm(), name);
}

sal::context* sal_state::get_context() const {
  return d_sal_context;
}

sal::module::ref sal_state::start_module() {
  push_scope(SCOPE_MODULE);
  sal::module::ref m = new sal::module(tm());
  d_current_module.push_back(m);
  return m;
}

void sal_state::finish_module(sal::module::ref m) {
  assert(d_current_module.back() == m);
  d_current_module.pop_back();
  pop_scope(SCOPE_MODULE);
  m->check_invariants();
  TRACE("parser::sal") << "finish_module: " << *m << std::endl;
}

void sal_state::add_context_parameters(const var_declarations_ctx& vars) {
  // Add variables to the symbol tables
  for (size_t i = 0; i < vars.var_names.size(); ++ i) {
    std::string name = vars.var_names[i];
    term_ref type = vars.var_types[i];
    term_ref var = new_variable(name, type, false);
    d_variables.add_entry(name, var);
    d_sal_context->add_parameter(name, var);
  }
}

term_ref sal_state::mk_term(term_op op, term_ref child) {
  return tm().mk_term(op, child);
}

term_ref sal_state::mk_term(term_op op, term_ref child1, term_ref child2) {
  return tm().mk_term(op, child1, child2);
}

term_ref sal_state::mk_tuple(const std::vector<term_ref>& elements) {
  assert(elements.size() > 1);
  return tm().mk_tuple(elements);
}

term_ref sal_state::mk_record(const term_manager::id_to_term_map& content) {
  assert(content.size() > 0);
  return tm().mk_record(content);
}

void sal_state::add_to_map(term_manager::id_to_term_map& map, std::string id, term_ref t) {
  term_manager::id_to_term_map::const_iterator it = map.find(id);
  if (it == map.end()) {
    map[id] = t;
  } else {
    throw parser_exception(id + " redeclared");
  }
}

sal::variable_class sal_state::get_lvalue_class(expr::term_ref lvalue) {
  // Go down the modules and see who can determine it
  std::vector<sal::module::ref>::reverse_iterator it = d_current_module.rbegin();
  for (; it != d_current_module.rend(); ++ it) {
    sal::module::ref m = *it;
    if (m->is_lvalue(lvalue)) {
      return m->get_lvalue_class(lvalue);
    }
  }
  // Didn't find it
  throw parser_exception(tm()) << "Expecting an lvalue, got " << lvalue << ".";
}

void sal_state::add_to_renaming_map(sal::module::id_to_lvalue& map, std::string id, term_ref lvalue) {
  sal::module::id_to_lvalue::const_iterator it = map.find(id);
  if (it == map.end()) {
    expr::term_ref lvalue_next = get_next_state_term(lvalue);
    sal::variable_class lvalue_class = get_lvalue_class(lvalue);
    map[id] = sal::module::lvalue_info(lvalue, lvalue_next, lvalue_class);
  } else {
    throw parser_exception(id + " redeclared");
  }
}

term_ref sal_state::mk_ite(const std::vector<term_ref>& ite_terms) {
  // if t0 then t1 elseif t2 then t3 ... elseif t_n-3 then t_n-2 else t_n-1
  assert(ite_terms.size() >= 3);
  assert(ite_terms.size() % 2 == 1);
  term_ref ite = ite_terms.back();
  for (int i = ite_terms.size() - 3; i >= 0; i -= 2) {
    ite = tm().mk_term(TERM_ITE, ite_terms[i], ite_terms[i+1], ite);
  }
  return ite;
}

term_ref sal_state::mk_subrange_type(term_ref b1, term_ref b2) {
  if (b1.is_null() && b2.is_null()) {
    return d_integer_type;
  }
  if (!b1.is_null() && !b2.is_null()) {
    term_ref ub = tm().mk_term(TERM_LEQ, d_x, b2);
    term_ref lb = tm().mk_term(TERM_GEQ, d_x, b1);
    term_ref body = tm().mk_term(TERM_AND, lb, ub);
    return tm().mk_predicate_subtype(d_x, body);
  } else if (b1.is_null()) {
    term_ref ub = tm().mk_term(TERM_LEQ, d_x, b2);
    return tm().mk_predicate_subtype(d_x, ub);
  } else {
    term_ref lb = tm().mk_term(TERM_GEQ, d_x, b1);
    return tm().mk_predicate_subtype(d_x, lb);
  }
}

void sal_state::define_constant(std::string id, term_ref type, term_ref definition) {
  TRACE("parser::sal") << "define_constant(" << id << ", " << type << ", " << definition << ")" << std::endl;
  if (tm().is_type(definition)) {
    define_type_in_scope(id, definition);
  } else {
    define_var_in_scope(id, type, definition);
  }
}

void sal_state::declare_constant(std::string id, term_ref type) {
  TRACE("parser::sal") << "declare_constant(" << id << ", " << type << ")" << std::endl;
  define_var_in_scope(id, type, new_variable(id, type, false));
}

void sal_state::define_type(std::string id, term_ref type) {
  TRACE("parser::sal") << "define_type(" << id << ", " << type << ")" << std::endl;
  define_type_in_scope(id, type);
}

void sal_state::add_assertion(std::string id, sal::assertion_form form, sal::module::ref m, term_ref assertion) {
  d_sal_context->add_assertion(id, form, m, assertion);
}

term_ref sal_state::mk_predicate_subtype(term_ref body) {
  assert(false);
  return term_ref();
}

term_ref sal_state::mk_enum_type(const std::vector<std::string>& ids) {
  std::set<std::string> id_set(ids.begin(), ids.end());
  if (id_set.size() != ids.size()) {
    throw exception("enumeration has repeating elements");
  }
  // Make the type
  term_ref type = tm().enum_type(ids);
  return type;
}

void sal_state::register_enumeration(term_ref enum_type) {
  // Register enum constants
  size_t enum_size = tm().get_enum_type_size(enum_type);
  for (size_t i = 0; i < enum_size; ++ i) {
    term_ref c = tm().mk_enum_constant(i, enum_type);
    define_var_in_scope(tm().get_enum_constant_id(c), enum_type, c);
  }
}

term_ref sal_state::mk_array_type(term_ref index_type, term_ref element_type) {
  TRACE("parser::sal") << "mk_array_type(" << index_type << ", " << element_type << ")" << std::endl;
  assert(!index_type.is_null());
  assert(!element_type.is_null());
  return tm().array_type(index_type, element_type);
}

term_ref sal_state::mk_record_type(const var_declarations_ctx& elements) {
  assert(elements.size() > 0);
  term_manager::id_to_term_map fields;
  for (size_t i = 0; i < elements.size(); ++ i) {
    fields[elements.var_names[i]] = elements.var_types[i];
  }
  return tm().record_type(fields);
}

void sal_state::start_module_declaration(const var_declarations_ctx& args) {
  // Declare all the variables
  push_scope(SCOPE_MODULE_DECLARATION);
  for (size_t i = 0; i < args.size(); ++ i) {
    std::string name = args.var_names[i];
    term_ref type = args.var_types[i];
    term_ref var = new_variable(name, type, false);
    d_variables.add_entry(name, var);
  }
}

void sal_state::finish_module_declaration(sal::module::ref m, const var_declarations_ctx& args) {
  // Add the variables to the module
  for (size_t i = 0; i < args.size(); ++ i) {
    std::string name = args.var_names[i];
    assert(d_variables.has_entry(name));
    term_ref var = d_variables.get_entry(name);
    m->add_parameter(name, var);
  }
  // Undeclare all the variables
  pop_scope(SCOPE_MODULE_DECLARATION);
}

void sal_state::define_module(std::string id, sal::module::ref m) {
  m->set_name(id);
  d_sal_context->add_module(id, m);
  if (d_modules.has_entry(id)) {
    throw parser_exception(id + " already declared");
  }
  d_modules.add_entry(id, m);
}

void sal_state::start_predicate_subtype(std::string id, term_ref base_type) {
  push_scope(SCOPE_PREDICATE_SUBTYPE);
  term_ref x = tm().mk_variable(id, base_type);
  define_var_in_scope(id, base_type, x);
}

term_ref sal_state::finish_predicate_subtype(term_ref predicate) {
  std::vector<term_ref> x;
  d_variables.get_scope_values(x);
  assert(x.size() == 1);
  term_ref result = tm().mk_predicate_subtype(x.back(), predicate);
  pop_scope(SCOPE_PREDICATE_SUBTYPE);
  return result;
}

void sal_state::start_quantifier(const var_declarations_ctx& bindings) {
  push_scope(SCOPE_QUANTIFIER);
  for (size_t i = 0; i < bindings.size(); ++ i) {
    std::string name = bindings.var_names[i];
    term_ref type = bindings.var_types[i];
    term_ref x = tm().mk_variable(name, type);
    define_var_in_scope(name, type, x);
  }
}

term_ref sal_state::mk_quantifier(term_op op, term_ref body) {
  term_ref result;
  std::vector<term_ref> x;
  d_variables.get_scope_values(x);
  switch (op) {
  case TERM_EXISTS:
    result = tm().mk_exists(x, body);
    break;
  case TERM_FORALL:
    result = tm().mk_forall(x, body);
    break;
  default:
    assert(false);
  }
  return result;
}

term_ref sal_state::finish_quantifier(term_op op, term_ref body) {
  term_ref result = mk_quantifier(op, body);
  pop_scope(SCOPE_QUANTIFIER);
  return result;
}

void sal_state::start_indexed_composition(const var_declarations_ctx& bindings) {
  push_scope(SCOPE_INDEXED_COMPOSITION);
  for (size_t i = 0; i < bindings.size(); ++ i) {
    std::string name = bindings.var_names[i];
    term_ref type = bindings.var_types[i];
    term_ref x = tm().mk_variable(name, type);
    define_var_in_scope(name, type, x);
  }
}

void sal_state::finish_indexed_composition(sal::module::ref m_from, sal::module::ref m_into, sal::composition_type comp_type) {
  std::vector<term_ref> x;
  d_variables.get_scope_values(x);
  // Take m_in and, depending on the composition type, quantify accordingly
  m_into->compose(*m_from, comp_type, x);
  pop_scope(SCOPE_INDEXED_COMPOSITION);
}


void sal_state::start_indexed_array(const var_declarations_ctx& bindings) {
  push_scope(SCOPE_INDEXED_ARRAY);
  assert(bindings.size() == 1);
  std::string name = bindings.var_names[0];
  term_ref type = bindings.var_types[0];
  term_ref x = tm().mk_variable(name, type);
  define_var_in_scope(name, type, x);
}

term_ref sal_state::finish_indexed_array(term_ref body) {
  std::vector<term_ref> x;
  d_variables.get_scope_values(x);
  assert(x.size() == 1);
  term_ref result = tm().mk_array_lambda(x[0], body);
  pop_scope(SCOPE_INDEXED_ARRAY);
  return result;
}

void sal_state::start_lambda(const var_declarations_ctx& bindings) {
  push_scope(SCOPE_LAMBDA);
  for (size_t i = 0; i < bindings.size(); ++ i) {
    std::string name = bindings.var_names[i];
    term_ref type = bindings.var_types[i];
    term_ref x = tm().mk_variable(name, type);
    define_var_in_scope(name, type, x);
  }
}

term_ref sal_state::finish_lambda(term_ref body) {
  std::vector<term_ref> args;
  d_variables.get_scope_values(args);
  term_ref result = (args.size() == 0 || body.is_null()) ? body : tm().mk_lambda(args, body);
  pop_scope(SCOPE_LAMBDA);
  return result;
}


void sal_state::define_var_in_scope(std::string id, term_ref type, term_ref term) {
  assert(!type.is_null());
  assert(!term.is_null());
  term_ref term_type = tm().type_of(term);
  if (!tm().compatible(term_type, type)) {
    throw parser_exception(tm()) << "types not compatible: got " << term_type << ", expected " << type;
  }
  d_variables.add_entry(id, term);
}

void sal_state::define_type_in_scope(std::string id, term_ref type) {
  assert(!type.is_null());
  d_types.add_entry(id, type);
}

term_ref sal_state::mk_array_read(term_ref a, term_ref i) {
  assert(false);
  return term_ref();
}

term_ref sal_state::mk_record_read(term_ref base, term_ref id) {
  assert(false);
  return term_ref();
}

term_ref sal_state::mk_term_access(term_ref base, term_ref accessor) {
  term_ref base_type = tm().type_of(base);
  if (tm().is_array_type(base_type)) {
    return tm().mk_array_read(base, accessor);
  } else if (tm().is_record_type(base_type)) {
    return tm().mk_record_read(base, accessor);
  } else {
    assert(false);
    return term_ref();
  }
}

term_ref sal_state::mk_term_access(term_ref base, const std::vector<term_ref>& accessors) {
  assert(!base.is_null());
  for (size_t i = 0; i < accessors.size(); ++ i) {
    base = mk_term_access(base, accessors[i]);
  }
  return base;
}

term_ref sal_state::mk_term_update(term_ref base, term_ref accessor, term_ref value) {
  term_ref base_type = tm().type_of(base);
  if (tm().is_array_type(base_type)) {
    return tm().mk_array_write(base, accessor, value);
  } else if (tm().is_record_type(base_type)) {
    return tm().mk_record_write(base, accessor, value);
  } else {
    assert(false);
    return term_ref();
  }
}

term_ref sal_state::mk_term_update(term_ref base, size_t i, const std::vector<term_ref>& accessors, term_ref value) {
  if (i + 1 == accessors.size()) {
    // Last one
    return mk_term_update(base, accessors[i], value);
  } else {
    // Example: a with [i][j] = v
    // write(a, i, // Update final
    //   write( // Update rest
    //       read(a, i), // Read term
    //       j, v
    //   )
    // )
    term_ref read_term = mk_term_access(base, accessors[i]);
    term_ref update_rest = mk_term_update(read_term, i+1, accessors, value);
    term_ref update_final = mk_term_update(base, accessors[i], update_rest);
    return update_final;
  }
}

term_ref sal_state::mk_term_update(term_ref base, const std::vector<term_ref>& accessors, term_ref value) {
  return mk_term_update(base, 0, accessors, value);
}

term_ref sal_state::mk_fun_app(term_ref f, const std::vector<term_ref>& args) {
  TRACE("parser::sal") << "mk_fun_app(" << f << " : " << tm().type_of(f) << ")" << std::endl;
  if (output::trace_tag_is_enabled("parser::sal")) {
    for (size_t i = 0; i < args.size(); ++ i) {
      TRACE("parser::sal") << i << " : " << args[i] << " : " << tm().type_of(args[i]) << std::endl;
    }
  }
  term_ref f_type = tm().type_of(f);
  if (tm().is_array_type(f_type) && args.size() == 1) {
    // Array types
    return tm().mk_array_read(f, args[0]);
  }
  // Function types
  return tm().mk_function_application(f, args);
}

sal::module::ref sal_state::composition(sal::module::ref m1, sal::module::ref m2, sal::composition_type type) {
  return m1->compose(*m2, type);
}

void sal_state::declare_variables(sal::module::ref m, sal::variable_class var_class, const var_declarations_ctx& vars) {
  for (size_t i = 0; i < vars.size(); ++ i) {
    std::string name = vars.var_names[i];
    term_ref type = vars.var_types[i];
    bool has_next = var_class != sal::SAL_VARIABLE_INPUT;
    term_ref var = new_variable(name, type, has_next);
    if (has_next) {
      expr::term_ref var_next = d_var_to_next_map[var];
      m->add_variable(name, var, var_class, var_next);
    } else {
      m->add_variable(name, var, var_class, expr::term_ref());
    }

    define_var_in_scope(name, type, var);
  }
}

void sal_state::declare_variables(const var_declarations_ctx& vars) {
  for (size_t i = 0; i < vars.size(); ++ i) {
    std::string name = vars.var_names[i];
    term_ref type = vars.var_types[i];
    term_ref var = new_variable(name, type, false);
    define_var_in_scope(name, type, var);
  }
}

void sal_state::load_module_variables(sal::module::ref m) {
  m->load_variables_into(d_variables);
}

void sal_state::load_module_to_module(sal::module::ref m_from, sal::module::ref m_to, symbol_override allow_override) {
  m_to->load(*m_from, allow_override);
}

void sal_state::load_module_to_module(sal::module::ref m_from, sal::module::ref m_to, const sal::module::id_to_lvalue& subst, symbol_override allow_override) {
  m_to->load(*m_from, subst, allow_override);
}

void sal_state::change_module_variables_to(sal::module::ref m, const var_declarations_ctx& vars, sal::variable_class var_class) {
  for (size_t i = 0; i < vars.var_names.size(); ++ i) {
    std::string id = vars.var_names[i];
    if (!m->has_variable(id, var_class)) {
      throw parser_exception(tm()) << id << " doesn't exists as " << var_class << " in the module";
    }
    m->change_variable_class(id, var_class);
  }
}

void sal_state::start_definition() {
  assert(!d_in_transition);
  d_lvalues.clear();
}

void sal_state::add_definition(sal::module::ref m, term_ref definition) {
  TRACE("parser::sal") << "add_definition(" << definition << ")" << std::endl;
  m->add_definition(definition);
}

void sal_state::end_definition() {
  d_lvalues.clear();
}

void sal_state::start_initialization() {
  assert(!false);
  d_lvalues.clear();
}

void sal_state::add_initialization(sal::module::ref m, term_ref initialization) {
  TRACE("parser::sal") << "add_initialization(" << initialization << ")" << std::endl;
  m->add_initialization(initialization);
  // Don't clear lvalues, initializations are taken together
}

void sal_state::end_initialization() {
  d_lvalues.clear();
}

void sal_state::start_transition() {
  d_in_transition = true;
  d_lvalues.clear();
}

bool sal_state::in_transition() const {
  return d_in_transition;
}

void sal_state::add_transition(sal::module::ref m, term_ref transition) {
  TRACE("parser::sal") << "add_transition(" << transition << ")" << std::endl;
  m->add_transition(transition);
  d_lvalues.clear();
}

void sal_state::end_transition() {
  d_in_transition = false;
  d_lvalues.clear();
}

/**
 * Commands can be either part of init or transition. At this point we don't
 * care, they should be well constructed.
 *
 * Basically, just do a disjunction of the commands.
 */
term_ref sal_state::mk_term_from_commands(const std::vector<term_ref>& cmds, bool has_else) {
  // Make a copy, to change the else command
  std::vector<term_ref> cmds_with_else(cmds);

  // If there is an else clause, we guard it with negation of other guards
  if (has_else) {
    if (d_guards.size() == 0) {
      throw parser_exception("ELSE not allowed on it's own");
    }
    term_ref any_guard = tm().mk_or(d_guards);
    term_ref else_guard = tm().mk_term(TERM_NOT, any_guard);
    cmds_with_else.back() = tm().mk_term(TERM_AND, else_guard, cmds_with_else.back());
  }

  // In the end, it's just a disjunction, picking one command
  term_ref result = tm().mk_or(cmds_with_else);
  return result;
}

/**
 * It's one guarded command, make the assertion that
 *
 *    guard & assignment & rest' = rest
 */
term_ref sal_state::mk_term_from_guarded(term_ref guard, const std::vector<term_ref>& assignments) {
  // TODO: assignments should be well-defined assignments (checked in assignment definition?)

  // Get the current module and all variables in it
  assert(d_current_module.size() > 0);
  sal::module::ref current_module = d_current_module.back();
  const sal::module::symbol_table& var_table = current_module->get_symbol_table();

  // Assertions
  std::vector<term_ref> assertions(assignments);

  // Add the guard if present
  if (!guard.is_null()) {
    assertions.push_back(guard);
  }

  // Add the rest' = rest
  sal::module::symbol_table::const_iterator it = var_table.begin();
  for (; it != var_table.end(); ++ it) {
    // Current state variable
    term_ref x = it->second.front();
    // If it appears in lvalues, it's constrainted so we skip it
    if (d_lvalues.count(x) > 0) continue; 
    sal::variable_class x_class = current_module->get_variable_class(x);
    switch (x_class) {
    case sal::SAL_VARIABLE_INPUT:
      // We don't constrain the input variables 
      break;
    case sal::SAL_VARIABLE_OUTPUT:
    case sal::SAL_VARIABLE_LOCAL:
    case sal::SAL_VARIABLE_GLOBAL: {
      term_ref x_next = get_next_state_variable(x);
      term_ref eq = tm().mk_term(TERM_EQ, x_next, x);
      assertions.push_back(eq);
      break;
    }
    default: 
      assert(false);
    }
  }

  // Final result
  term_ref result = tm().mk_and(assertions);
  return result;
}

void sal_state::start_constant_declaration(std::string id, const var_declarations_ctx& args, term_ref type) {
  if (args.size() > 0) {
    // Declare the function (in case of recursion)
    std::vector<term_ref> arg_types(args.var_types);
    arg_types.push_back(type);
    term_ref fun_type = tm().function_type(arg_types);
    term_ref fun = tm().mk_variable(id, fun_type);
    define_constant(id, fun_type, fun);
    // Start a lambda
    start_lambda(args);
  }
}

void sal_state::finish_constant_declaration(std::string id, const var_declarations_ctx& args, term_ref type, term_ref definition) {
  // Finish the lambda
  if (args.size() > 0) {
    definition = finish_lambda(definition);
    if (!definition.is_null()) {
      term_ref fun = get_variable(id, false);
      assert(d_fun_to_definition_map.find(fun) == d_fun_to_definition_map.end());
      d_fun_to_definition_map[fun] = definition;
    }
  } else {
    if (!definition.is_null()) {
      define_constant(id, type, definition);
    } else if (!tm().is_function_type(type)) {
      declare_constant(id, type);
    }
  }
}

void sal_state::check_term(term_ref t) const {
  if (t.is_null()) {
    throw parser_exception("internal parsing error");
  }
}

void sal_state::check_index_type(term_ref t) const {
  const term& t_term = tm().term_of(t);
  // We can index with Boolean types
  if (t_term.op() == TYPE_BOOL) return;
  // We can index with integer types
  if (tm().is_integer_type(t)) return;
  // Otherwise, we need to bail
  throw parser_exception("index type must be finite");
}

void sal_state::start_set_abstraction(term_ref lhs, std::string id, term_ref type) {
  push_scope(SCOPE_SET_ABSTRACTION);
  define_var_in_scope(id, type, lhs);
}

void sal_state::sal_state::end_set_abstraction() {
  pop_scope(SCOPE_SET_ABSTRACTION);
}

term_ref sal_state::mk_set_enumeration(term_ref t, const std::vector<term_ref>& set_elements) {
  if (set_elements.size() == 0) { return tm().mk_boolean_constant(false); }
  std::vector<term_ref> equalities;
  for (size_t i = 0; i < set_elements.size(); ++ i) {
    equalities.push_back(tm().mk_term(TERM_EQ, t, set_elements[i]));
  }
  return tm().mk_term(TERM_OR, equalities);
}

void sal_state::guards_add(term_ref t) {
  if (d_multi_commands > 0) {
    d_multi_guard = t;
  } else {
    d_guards.insert(t);
  }
}

void sal_state::guards_clear() {
  d_guards.clear();
}

void sal_state::lvalues_clear() {
  d_lvalues.clear();
}

void sal_state::lvalues_add(term_ref t) {

  // Get the actual variable of the lvalue (extract arrays);
  bool done = false;
  while (!done) {
    const term& t_term = tm().term_of(t);
    term_op op = t_term.op();
    switch (op) {
    case TERM_ARRAY_READ:
      t = t_term[0];
      break;
    case TERM_RECORD_READ:
      t = t_term[0];
      break;
    case VARIABLE:
      done = true;
      break;
    default:
      throw parser_exception(tm()) << "Unexpected lvalue: " << t;
      break;
    }
  }

  // Get the current variable (will throw if t_next is not in next)
  if (d_in_transition) {
    t = get_state_variable(t);
  }

  // Check if has already been defined 
  if (d_lvalues.count(t) > 0) {
     throw parser_exception(tm()) << "Duplicate lvalue: " << t;
  }

  // Check if input variable
  sal::module::ref current_module = d_current_module.back();
  if (current_module->get_variable_class(t) == sal::SAL_VARIABLE_INPUT) {
    throw parser_exception(tm()) << "Lvalue " << t << " is over input variables!";
  }

  // Otherwise add it
  TRACE("parser::sal::lvalue") << "adding lvalue: " << t << std::endl; 
  d_lvalues.insert(t);
}

void sal_state::start_multi_command() {
  d_multi_commands ++;
}

void sal_state::end_multi_command() {
  assert(d_multi_commands > 0);
  assert(!d_multi_guard.is_null());
  d_multi_guard = mk_quantifier(TERM_EXISTS, d_multi_guard);
  d_multi_commands --;
  if (d_multi_commands == 0) {
    d_guards.insert(d_multi_guard);
    d_multi_guard = term_ref();
  }
}

term_ref sal_state::mk_assignment(term_ref lvalue, term_ref rhs) {
  if (tm().term_of(lvalue).op() == VARIABLE || !d_in_transition) {
    return tm().mk_term(TERM_EQ, lvalue, rhs);
  } else {

    // Collect the accessors
    std::vector<term_ref> accessors;
    for (bool done = false; !done;) {
      const term& t = tm().term_of(lvalue);
      term_op op = t.op();
      switch (op) {
      case TERM_ARRAY_READ:
        lvalue = t[0];
        accessors.push_back(t[1]);
        break;
      case TERM_RECORD_READ:
        lvalue = t[0];
        accessors.push_back(t[1]);
        break;
      case VARIABLE:
        done = true;
        break;
      default:
        throw parser_exception(tm()) << "Unexpected lvalue: " << lvalue;
        break;
      }
    }

    // Get the state version of lvalue
    term_ref lvalue_prev = get_state_variable(lvalue);

    // Now, make a proper term update
    term_ref new_rhs = mk_term_update(lvalue_prev, accessors, rhs);
    term_ref result = tm().mk_term(TERM_EQ, lvalue, new_rhs);
    return result;
  }
}

void sal_state::module_modify_local(sal::module::ref m, sal::module::ref m_local, const var_declarations_ctx& var_ctx) {
  TRACE("parser::sal") << "sal_state::module_modify_local: m = " << *m << std::endl;
  TRACE("parser::sal") << "sal_state::module_modify_local: m_local = " << *m_local << std::endl;
  load_module_to_module(m_local, m, sal::module::SYMBOL_OVERRIDE_NO);
  change_module_variables_to(m, var_ctx, sal::SAL_VARIABLE_LOCAL);
}

void sal_state::module_modify_output(sal::module::ref m, sal::module::ref m_output, const var_declarations_ctx& var_ctx) {
  TRACE("parser::sal") << "sal_state::module_modify_output: m = " << *m << std::endl;
  TRACE("parser::sal") << "sal_state::module_modify_output: m_local = " << *m_output << std::endl;
  load_module_to_module(m_output, m, sal::module::SYMBOL_OVERRIDE_NO);
  change_module_variables_to(m, var_ctx, sal::SAL_VARIABLE_OUTPUT);
}

void sal_state::module_modify_rename(sal::module::ref m, sal::module::ref m_rename, const sal::module::id_to_lvalue& subst_map) {
  TRACE("parser::sal") << "sal_state::module_modify_rename: m = " << *m << std::endl;
  load_module_to_module(m_rename, m, subst_map, sal::module::SYMBOL_OVERRIDE_YES_EQ);
}

void sal_state::module_modify_with(sal::module::ref m, sal::module::ref m_with) {
  TRACE("parser::sal") << "sal_state::module_modify_with: m = " << *m << std::endl;
  TRACE("parser::sal") << "sal_state::module_modify_with: m_width = " << *m << std::endl;
  load_module_to_module(m_with, m, sal::module::SYMBOL_OVERRIDE_YES_EQ);
}
