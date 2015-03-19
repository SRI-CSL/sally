/*
 * parser_state.cpp
 *
 *  Created on: Nov 6, 2014
 *      Author: dejan
 */

#include "parser/sal/sal_state.h"
#include "parser/parser.h"

#include "expr/term_manager.h"

#include <cassert>

using namespace sally;
using namespace parser;
using namespace expr;

using namespace std;

sal_state::sal_state(const system::context& context)
: d_context(context)
, d_variables("local vars")
, d_types("types")
{
  // Add the basic types
  term_manager& tm = context.tm();
  d_types.add_entry("Real", term_ref_strong(tm, tm.real_type()));
  d_types.add_entry("Boolean", term_ref_strong(tm, tm.boolean_type()));
  d_types.add_entry("Integer", term_ref_strong(tm, tm.integer_type()));
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

term_ref sal_state::get_variable(std::string id) const {
  if (!d_variables.has_entry(id)) {
    throw parser_exception(id + "undeclared");
  }
  return d_variables.get_entry(id);
}

system::state_type* sal_state::mk_state_type(std::string id, const std::vector<std::string>& vars, const std::vector<expr::term_ref>& types) const {
  expr::term_ref type = tm().mk_struct_type(vars, types);
  return new system::state_type(tm(), id, type);
}

system::state_formula* sal_state::mk_state_formula(std::string id, std::string type_id, expr::term_ref sf) const {
  system::state_type* st = ctx().get_state_type(type_id);
  return new system::state_formula(tm(), st, sf);
}

system::transition_formula* sal_state::mk_transition_formula(std::string id, std::string type_id, expr::term_ref tf) const {
  system::state_type* st = ctx().get_state_type(type_id);
  return new system::transition_formula(tm(), st, tf);
}

system::transition_system* sal_state::mk_transition_system(std::string id, std::string type_id, std::string init_id, const std::vector<std::string>& transition_ids) {
  system::state_type* st = ctx().get_state_type(type_id);
  const system::state_formula* init = ctx().get_state_formula(init_id);
  std::vector<const system::transition_formula*> transitions;
  for (size_t i = 0; i < transition_ids.size(); ++ i) {
    transitions.push_back(ctx().get_transition_formula(transition_ids[i]));
  }
  return new system::transition_system(st, init, transitions);
}

void sal_state::use_state_type(std::string id, system::state_type::var_class var_class, bool use_namespace) {
  system::state_type* st = d_context.get_state_type(id);
  use_state_type(st, var_class, use_namespace);
}

void sal_state::use_state_type(system::state_type* st, system::state_type::var_class var_class, bool use_namespace) {

  // Use the appropriate namespace
  st->use_namespace();
  if (use_namespace) {
    st->use_namespace(var_class);
  }

  // Declare the variables
  const std::vector<expr::term_ref>& vars = st->get_variables(var_class);
  for (size_t i = 0; i < vars.size(); ++ i) {
    const term& var_term = tm().term_of(vars[i]);
    std::string var_name = tm().get_variable_name(var_term);
    d_variables.add_entry(var_name, vars[i]);
  }

  // Pop the namespace
  tm().pop_namespace();
  if (use_namespace) {
    tm().pop_namespace();
  }
}

void sal_state::push_scope() {
  d_variables.push_scope();
}

void sal_state::pop_scope() {
  d_variables.pop_scope();
}

void sal_state::ensure_declared(std::string id, sal_object type, bool declared) {
  bool ok = declared;
  switch (type) {
  case SAL_VARIABLE:
    ok = d_variables.has_entry(id);
    break;
  case SAL_TYPE:
    ok = d_types.has_entry(id);
    break;
  case SAL_STATE_TYPE:
    ok = d_context.has_state_type(id);
    break;
  case SAL_STATE_FORMULA:
    ok = d_context.has_state_formula(id);
    break;
  case SAL_TRANSITION_FORMULA:
    ok = d_context.has_transition_formula(id);
    break;
  case SAL_TRANSITION_SYSTEM:
    ok = d_context.has_transition_system(id);
    break;
  case SAL_OBJECT_LAST:
    // Always noop
    return;
  default:
    assert(false);
  }

  if (ok != declared) {
    if (declared) throw parser_exception(id + " not declared");
    else throw parser_exception(id + " already declared");
  }
}
