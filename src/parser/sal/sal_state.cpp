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

#include "expr/term_manager.h"
#include "expr/gc_relocator.h"

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

system::state_type* sal_state::mk_state_type(std::string id,
    const std::vector<std::string>& state_vars, const std::vector<expr::term_ref>& state_types,
    const std::vector<std::string>& input_vars, const std::vector<expr::term_ref>& input_types) const
{
  expr::term_ref state_type = tm().mk_struct_type(state_vars, state_types);
  expr::term_ref input_type = tm().mk_struct_type(input_vars, input_types);
  return new system::state_type(id, tm(), state_type, input_type);
}

system::state_formula* sal_state::mk_state_formula(std::string id, std::string type_id, expr::term_ref sf) const {
  const system::state_type* st = ctx().get_state_type(type_id);
  return new system::state_formula(tm(), st, sf);
}

system::transition_formula* sal_state::mk_transition_formula(std::string id, std::string type_id, expr::term_ref tf) const {
  const system::state_type* st = ctx().get_state_type(type_id);
  return new system::transition_formula(tm(), st, tf);
}

void sal_state::use_state_type(std::string id, system::state_type::var_class var_class, bool use_namespace) {
  const system::state_type* st = d_context.get_state_type(id);
  use_state_type(st, var_class, use_namespace);
}

void sal_state::use_state_type(const system::state_type* st, system::state_type::var_class var_class, bool use_namespace) {

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
    d_variables.add_entry(var_name, expr::term_ref_strong(tm(), vars[i]));
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

void sal_state::gc_collect(const expr::gc_relocator& gc_reloc) {
  d_variables.gc_relocate(gc_reloc);
  d_types.gc_relocate(gc_reloc);
}
