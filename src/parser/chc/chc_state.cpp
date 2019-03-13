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

#include "chc_state.h"
#include "parser/parser.h"

#include "expr/term_manager.h"
#include "expr/gc_relocator.h"

#include "utils/trace.h"

#include <cassert>

using namespace sally;
using namespace parser;
using namespace expr;

using namespace std;

chc_state::chc_state(const system::context& context)
: d_context(context)
, d_system(context)
, d_variables("local vars")
, d_types("types")
, d_functions("predicates")
, d_finalized(false)
{
  // Add the basic types
  term_manager& tm = context.tm();
  d_types.add_entry("Real", term_ref_strong(tm, tm.real_type()));
  d_types.add_entry("Bool", term_ref_strong(tm, tm.boolean_type()));
  d_types.add_entry("Int", term_ref_strong(tm, tm.integer_type()));
}

string chc_state::token_text(pANTLR3_COMMON_TOKEN token) {
  ANTLR3_MARKER start = token->getStartIndex(token);
  size_t size = token->getStopIndex(token) - start + 1;
  return string((const char*) start, size);
}

term_ref chc_state::get_type(std::string id) const {
  if (!d_types.has_entry(id)) {
    throw parser_exception(id + " undeclared");
  }
  return d_types.get_entry(id);
}

term_ref chc_state::get_bitvector_type(size_t size) const {
  return tm().bitvector_type(size);
}

term_ref chc_state::get_variable(std::string id) const {
  if (!d_variables.has_entry(id)) {
    throw parser_exception(id + "undeclared");
  }
  return d_variables.get_entry(id);
}

term_ref chc_state::get_function(std::string id) const {
  if (!d_functions.has_entry(id)) {
    throw parser_exception(id + "undeclared");
  }
  return d_functions.get_entry(id);
}

void chc_state::set_variable(std::string id, expr::term_ref t) {
  d_variables.add_entry(id, expr::term_ref_strong(tm(), t));
}

void chc_state::push_scope() {
  d_variables.push_scope();
}

void chc_state::pop_scope() {
  d_variables.pop_scope();
}

bool chc_state::is_declared(std::string id, chc_object type) const {
  switch (type) {
  case CHC_VARIABLE:
    return d_variables.has_entry(id);
    break;
  case CHC_TYPE:
    return d_types.has_entry(id);
    break;
  case CHC_PREDICATE:
    return d_functions.has_entry(id);
    break;
  case CHC_OBJECT_LAST:
    // Always no op
    return false;
  default:
    assert(false);
  }

  return false;
}

void chc_state::ensure_declared(std::string id, chc_object type, bool declared) const {
  if (declared != is_declared(id, type)) {
    if (declared) throw parser_exception(id + " not declared");
    else throw parser_exception(id + " already declared");
  }
}

void chc_state::gc_collect(const expr::gc_relocator& gc_reloc) {
  d_variables.gc_relocate(gc_reloc);
  d_types.gc_relocate(gc_reloc);
  d_functions.gc_relocate(gc_reloc);
}

void chc_state::declare_variable(std::string id, term_ref type) {
  term_ref var = tm().mk_variable(id, type);
  d_variables.add_entry(id, term_ref_strong(tm(), var));
}

void chc_state::declare_function(std::string id, const std::vector<expr::term_ref>& signature) {
  term_ref f_type = tm().function_type(signature);
  term_ref f = tm().mk_variable(id, f_type);
  d_functions.add_entry(id, term_ref_strong(tm(), f));
}

void chc_state::assert_chc(expr::term_ref head, expr::term_ref tail) {
  TRACE("chc::parse") << "chc rule: " << head << " <- " << tail << std::endl;
  d_system.add_rule(head, tail);
}

cmd::command* chc_state::finalize() {
  if (d_finalized) { return 0; }
  d_finalized = true;
  return d_system.to_commands();
}

