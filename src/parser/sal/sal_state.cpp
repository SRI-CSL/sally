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
#include "parser/command.h"

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

term_ref sal_state::new_variable(std::string name, term_ref type) {
  term_ref var = tm().mk_variable(name, type);
  term_ref var_next = tm().mk_variable(name + "'", type);
  assert(d_var_to_next_map.find(var) == d_var_to_next_map.end());
  d_var_to_next_map[var] = var_next;
  return var;
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

void sal_state::push_scope() {
  d_variables.push_scope();
  d_types.push_scope();
}

void sal_state::pop_scope() {
  d_variables.pop_scope();
  d_types.pop_scope();
}

void sal_state::gc_collect(const gc_relocator& gc_reloc) {
  d_variables.gc_relocate(gc_reloc);
  d_types.gc_relocate(gc_reloc);
}

command* sal_state::finalize() {
  return 0;
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

sal::context* sal_state::new_context(std::string name) {
  d_sal_context = new sal::context(tm(), name);
  return d_sal_context;
}

sal::module::ref sal_state::start_module() {
  push_scope();
  return new sal::module(tm());
}

void sal_state::finish_module(sal::module::ref m) {
  TRACE("parser::sal") << "finish_module: " << *m << std::endl;
}

void sal_state::add_context_parameters(const var_declarations_ctx& vars) {
  // Add variables to the symbol tables
  for (size_t i = 0; i < vars.var_names.size(); ++ i) {
    std::string name = vars.var_names[i];
    term_ref type = vars.var_types[i];
    term_ref var = new_variable(name, type);
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

term_ref sal_state::mk_record(const expr::term_manager::id_to_term_map& content) {
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
  define_var_in_scope(id, type, new_variable(id, type));
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
  push_scope();
  for (size_t i = 0; i < args.size(); ++ i) {
    std::string name = args.var_names[i];
    term_ref type = args.var_types[i];
    term_ref var = new_variable(name, type);
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
  pop_scope();
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
  push_scope();
  term_ref x = tm().mk_variable(id, base_type);
  define_var_in_scope(id, base_type, x);
  push_scope();
}

term_ref sal_state::finish_predicate_subtype(term_ref predicate) {
  pop_scope();
  std::vector<term_ref> x;
  d_variables.get_scope_values(x);
  assert(x.size() == 1);
  term_ref result = tm().mk_predicate_subtype(x.back(), predicate);
  pop_scope();
  return result;
}

void sal_state::start_quantifier(const var_declarations_ctx& bindings) {
  push_scope();
  for (size_t i = 0; i < bindings.size(); ++ i) {
    std::string name = bindings.var_names[i];
    term_ref type = bindings.var_types[i];
    term_ref x = tm().mk_variable(name, type);
    define_var_in_scope(name, type, x);
  }
  push_scope();
}

term_ref sal_state::finish_quantifier(term_op op, term_ref body) {
  term_ref result;
  pop_scope();
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
  pop_scope();
  return result;
}

void sal_state::start_indexed_composition(const var_declarations_ctx& bindings) {
  push_scope();
  for (size_t i = 0; i < bindings.size(); ++ i) {
    std::string name = bindings.var_names[i];
    term_ref type = bindings.var_types[i];
    term_ref x = tm().mk_variable(name, type);
    define_var_in_scope(name, type, x);
  }
  push_scope();
}

void sal_state::finish_indexed_composition(sal::module::ref m_from, sal::module::ref m_into, sal::composition_type comp_type) {
  pop_scope();
  std::vector<term_ref> x;
  d_variables.get_scope_values(x);
  // Take m_in and, depending on the composition type, quantify accordingly
  m_into->compose(*m_from, comp_type, x);
  pop_scope();
}


void sal_state::start_indexed_array(const var_declarations_ctx& bindings) {
  push_scope();
  assert(bindings.size() == 1);
  std::string name = bindings.var_names[0];
  term_ref type = bindings.var_types[0];
  term_ref x = tm().mk_variable(name, type);
  define_var_in_scope(name, type, x);
  push_scope();
}

term_ref sal_state::finish_indexed_array(term_ref body) {
  pop_scope();
  std::vector<term_ref> x;
  d_variables.get_scope_values(x);
  assert(x.size() == 1);
  term_ref result = tm().mk_array_lambda(x[0], body);
  pop_scope();
  return result;
}

void sal_state::start_lambda(const var_declarations_ctx& bindings) {
  push_scope();
  for (size_t i = 0; i < bindings.size(); ++ i) {
    std::string name = bindings.var_names[i];
    term_ref type = bindings.var_types[i];
    term_ref x = tm().mk_variable(name, type);
    define_var_in_scope(name, type, x);
  }
  push_scope();
}

term_ref sal_state::finish_lambda(term_ref body) {
  pop_scope();
  std::vector<term_ref> args;
  d_variables.get_scope_values(args);
  term_ref result = (args.size() == 0 || body.is_null()) ? body : tm().mk_lambda(args, body);
  pop_scope();
  return result;
}


void sal_state::define_var_in_scope(std::string id, term_ref type, term_ref term) {
  // TODO: check that the types match
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
    term_ref var = new_variable(name, type);
    m->add_variable(name, var, var_class);
    define_var_in_scope(name, type, var);
  }
}

void sal_state::declare_variables(const var_declarations_ctx& vars) {
  for (size_t i = 0; i < vars.size(); ++ i) {
    std::string name = vars.var_names[i];
    term_ref type = vars.var_types[i];
    term_ref var = new_variable(name, type);
    define_var_in_scope(name, type, var);
  }
}

void sal_state::load_module_variables(sal::module::ref m) {
  m->load_variables_into(d_variables);
}

void sal_state::load_module_to_module(sal::module::ref m_from, sal::module::ref m_to) {
  m_to->load(*m_from);
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

void sal_state::add_definition(sal::module::ref m, term_ref definition) {
  TRACE("parser::sal") << "add_definition(" << definition << ")" << std::endl;
  m->add_definition(definition);
}

void sal_state::add_initialization(sal::module::ref m, term_ref initialization) {
  TRACE("parser::sal") << "add_initialization(" << initialization << ")" << std::endl;
  m->add_initialization(initialization);
}

void sal_state::add_transition(sal::module::ref m, term_ref transition) {
  TRACE("parser::sal") << "add_transition(" << transition << ")" << std::endl;
  m->add_transition(transition);
}

void sal_state::add_invariant(sal::module::ref m, term_ref invariant) {
  TRACE("parser::sal") << "add_invariant(" << invariant << ")" << std::endl;
  m->add_invariant(invariant);
}

void sal_state::add_init_formula(sal::module::ref m, term_ref init_formula) {
  TRACE("parser::sal") << "add_init_formula(" << init_formula << ")" << std::endl;
  m->add_init_formula(init_formula);
}

term_ref sal_state::mk_term_from_commands(const std::vector<term_ref>& cmds) {
  assert(false);
  return term_ref();
}

term_ref sal_state::mk_term_from_guarded(term_ref guards, const std::vector<term_ref>& assignments) {
  assert(false);
  return term_ref();
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
  push_scope();
  define_var_in_scope(id, type, lhs);
}

void sal_state::sal_state::end_set_abstraction() {
  pop_scope();
}

term_ref sal_state::mk_set_enumeration(term_ref t, const std::vector<term_ref>& set_elements) {
  if (set_elements.size() == 0) { return tm().mk_boolean_constant(false); }
  std::vector<term_ref> equalities;
  for (size_t i = 0; i < set_elements.size(); ++ i) {
    equalities.push_back(tm().mk_term(TERM_EQ, t, set_elements[i]));
  }
  return tm().mk_term(TERM_OR, equalities);
}
