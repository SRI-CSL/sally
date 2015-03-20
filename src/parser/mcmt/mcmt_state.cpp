/*
 * parser_state.cpp
 *
 *  Created on: Nov 6, 2014
 *      Author: dejan
 */

#include "parser/mcmt/mcmt_state.h"
#include "parser/parser.h"

#include "expr/term_manager.h"

#include <cassert>

using namespace sally;
using namespace parser;
using namespace expr;

using namespace std;

mcmt_state::mcmt_state(const system::context& context)
: d_context(context)
, d_variables("local vars")
, d_types("types")
{
  // Add the basic types
  term_manager& tm = context.tm();
  d_types.add_entry("Real", term_ref_strong(tm, tm.real_type()));
  d_types.add_entry("Bool", term_ref_strong(tm, tm.boolean_type()));
  d_types.add_entry("Integer", term_ref_strong(tm, tm.integer_type()));
}

string mcmt_state::token_text(pANTLR3_COMMON_TOKEN token) {
  ANTLR3_MARKER start = token->getStartIndex(token);
  size_t size = token->getStopIndex(token) - start + 1;
  return string((const char*) start, size);
}

term_ref mcmt_state::get_type(std::string id) const {
  if (!d_types.has_entry(id)) {
    throw parser_exception(id + " undeclared");
  }
  return d_types.get_entry(id);
}

term_ref mcmt_state::get_variable(std::string id) const {
  if (!d_variables.has_entry(id)) {
    throw parser_exception(id + "undeclared");
  }
  return d_variables.get_entry(id);
}

void mcmt_state::set_variable(std::string id, expr::term_ref t) {
  d_variables.add_entry(id, t);
}


system::state_type* mcmt_state::mk_state_type(std::string id, const std::vector<std::string>& vars, const std::vector<expr::term_ref>& types) const {
  expr::term_ref type = tm().mk_struct_type(vars, types);
  return new system::state_type(tm(), id, type);
}

system::state_formula* mcmt_state::mk_state_formula(std::string id, std::string type_id, expr::term_ref sf) const {
  system::state_type* st = ctx().get_state_type(type_id);
  system::state_formula* result = new system::state_formula(tm(), st, sf);
  result->set_id(id);
  return result;
}

system::transition_formula* mcmt_state::mk_transition_formula(std::string id, std::string type_id, expr::term_ref tf) const {
  system::state_type* st = ctx().get_state_type(type_id);
  system::transition_formula* result = new system::transition_formula(tm(), st, tf);
  result->set_id(id);
  return result;
}

system::transition_system* mcmt_state::mk_transition_system(std::string id, std::string type_id, std::string init_id, std::string transition_id) {
  system::state_type* st = ctx().get_state_type(type_id);
  const system::state_formula* init = ctx().get_state_formula(init_id);
  const system::transition_formula* transition = ctx().get_transition_formula(transition_id);
  return new system::transition_system(st, init, transition);
}

void mcmt_state::use_state_type(std::string id, system::state_type::var_class var_class, bool use_namespace) {
  system::state_type* st = d_context.get_state_type(id);
  use_state_type(st, var_class, use_namespace);
}

void mcmt_state::use_state_type(system::state_type* st, system::state_type::var_class var_class, bool use_namespace) {

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

  // Declare all the state formulas of this stype
  system::state_type::formula_set::const_iterator it = st->state_formulas_begin();
  for (; it != st->state_formulas_end(); ++ it) {
    const system::state_formula* f = *it;
    // If the formula has an id, add it
    if (!f->get_id().empty()) {
      // Get the term of the formula and transform the variables if going to the next state
      expr::term_ref f_term = f->get_formula();
      if (var_class == system::state_type::STATE_NEXT) {
        f_term = st->change_formula_vars(system::state_type::STATE_CURRENT, var_class, f_term);
      }
      // Get the id and turn it into a state type proper id
      std::string id = st->get_canonical_name(f->get_id(), var_class);
      // Add to variable table
      d_variables.add_entry(id, f_term);
    }
  }

  // Pop the namespace
  tm().pop_namespace();
  if (use_namespace) {
    tm().pop_namespace();
  }
}

void mcmt_state::use_state_type_and_transitions(system::state_type* st) {
  // Use the current state
  use_state_type(st, system::state_type::STATE_CURRENT, lsal_extensions());
  // Use the next stat
  use_state_type(st, system::state_type::STATE_NEXT, false);
  // Use all the transition formulas
  system::state_type::transition_formula_set::const_iterator it = st->transition_formulas_begin();
  for (; it != st->transition_formulas_end(); ++ it) {
    const system::transition_formula* f = *it;
    // If the formula has an id, add it
    if (!f->get_id().empty()) {
      // Add to variable table
      d_variables.add_entry(f->get_id(), f->get_formula());
    }
  }
}

void mcmt_state::push_scope() {
  d_variables.push_scope();
}

void mcmt_state::pop_scope() {
  d_variables.pop_scope();
}

bool mcmt_state::is_declared(std::string id, mcmt_object type) const {
  switch (type) {
  case MCMT_VARIABLE:
    return d_variables.has_entry(id);
    break;
  case MCMT_TYPE:
    return d_types.has_entry(id);
    break;
  case MCMT_STATE_TYPE:
    return d_context.has_state_type(id);
    break;
  case MCMT_STATE_FORMULA:
    return d_context.has_state_formula(id);
    break;
  case MCMT_TRANSITION_FORMULA:
    return d_context.has_transition_formula(id);
    break;
  case MCMT_TRANSITION_SYSTEM:
    return d_context.has_transition_system(id);
    break;
  case MCMT_OBJECT_LAST:
    // Always no op
    return false;
  default:
    assert(false);
  }

  return false;
}

void mcmt_state::ensure_declared(std::string id, mcmt_object type, bool declared) const {
  if (declared != is_declared(id, type)) {
    if (declared) throw parser_exception(id + " not declared");
    else throw parser_exception(id + " already declared");
  }
}

/**
 * Make a condition term:
 * if c[0] then c[1]
 * elif c[2] then c[3]
 * ...
 * else c[2n]
 */
expr::term_ref mcmt_state::mk_cond(const std::vector<expr::term_ref>& children) {
  assert(children.size() & 1);
  assert(children.size() >= 3);

  expr::term_ref result = children.back();
  for (int i = children.size() - 3; i >= 0; i -= 2) {
    result = tm().mk_term(expr::TERM_ITE, children[i], children[i+1], result);
  }
  return result;
}

bool mcmt_state::lsal_extensions() const {
  return ctx().get_options().get_bool("lsal-extensions");
}

