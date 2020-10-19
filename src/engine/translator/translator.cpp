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

#include "engine/translator/translator.h"

#include "smt/factory.h"
#include "utils/output.h"

#include <sstream>
#include <iostream>
#include <algorithm>
#include <cassert>

namespace sally {
namespace output {

translator::translator(const system::context& ctx)
: engine(ctx)
, d_ts(0)
, d_sf(0)
{
}

translator::~translator() {
}

void translator::to_stream_mcmt(std::ostream& out) const {

  // Output the state type
  const system::state_type* state_type = d_ts->get_state_type();
  state_type->use_namespace();
  out << ";; State type" << std::endl;
  out << "(define-state-type state_type " << state_type->get_state_type_var() << " " << state_type->get_input_type_var() << ")" << std::endl;
  out << std::endl;

  // Output the initial state
  state_type->use_namespace(system::state_type::STATE_CURRENT);
  expr::term_ref initial_states = d_ts->get_initial_states();
  out << ";; Initial states" << std::endl;
  out << "(define-states initial_states state_type " << initial_states << ")" << std::endl;
  out << std::endl;
  ctx().tm().pop_namespace();

  // Output the transition relation
  expr::term_ref transition_relation = d_ts->get_transition_relation();
  out << ";; Transition relation" << std::endl;
  out << "(define-transition transition state_type " << transition_relation << ")" << std::endl;
  out << std::endl;

  // Output the transition system
  out << ";; Transition system" << std::endl;
  out << "(define-transition-system T state_type initial_states transition)" << std::endl;
  out << std::endl;

  // Output the query
  state_type->use_namespace(system::state_type::STATE_CURRENT);
  out << ";; Query " << std::endl;
  out << "(query T " << d_sf->get_formula() << ")" << std::endl;
  ctx().tm().pop_namespace();

  // State type namespace
  ctx().tm().pop_namespace();
}

class nuxmv_name_transformer : public utils::name_transformer {
public:
  std::string apply(std::string id) const {
    // state.x => x
    if (6 < id.size() && id.substr(0, 6) == "state.") {
      id = id.substr(6);
    } else
    // input.x => x
    if (6 < id.size() && id.substr(0, 6) == "input.") {
        id = id.substr(6);
      } else
    // next.x => next(x)
    if (5 < id.size() && id.substr(0, 5) == "next.") {
      id = std::string("next(") + id.substr(5) + std::string(")");
    }
    // Replace any bad characters
    std::replace(id.begin(), id.end(), '!', '_');
    return id;
  }
};

void translator::to_stream_nuxmv(std::ostream& out) const {

  // Name transformer
  nuxmv_name_transformer* name_transformer = new nuxmv_name_transformer();
  tm().set_name_transformer(name_transformer);

  // The state type
  const system::state_type* st = d_ts->get_state_type();
  st->use_namespace();

  out << "MODULE main" << std::endl;

  // Declare state variables
  const std::vector<expr::term_ref>& state_vars = st->get_variables(system::state_type::STATE_CURRENT);
  out << "VAR" << std::endl;
  for (size_t i = 0; i < state_vars.size(); ++ i) {
    expr::term_ref var = state_vars[i];
    const expr::term& var_term = tm().term_of(var);
    std::string var_name = name_transformer->apply(tm().get_variable_name(var_term));
    out << "    " << var_name << ": " << tm().type_of(var_term) << ";" << std::endl;
  }
  out << std::endl;

  const std::vector<expr::term_ref>& input_vars = st->get_variables(system::state_type::STATE_INPUT);
  if (input_vars.size() > 0) {
    out << "IVAR" << std::endl;
    for (size_t i = 0; i < input_vars.size(); ++ i) {
      expr::term_ref var = input_vars[i];
      const expr::term& var_term = tm().term_of(var);
      std::string var_name = name_transformer->apply(tm().get_variable_name(var_term));
      out << "    " << var_name << ": " << tm().type_of(var_term) << ";" << std::endl;
    }
    out << std::endl;
  }

  // Get the let definitions
  const expr::term& trans = tm().term_of(d_ts->get_transition_relation());
  const expr::term& init = tm().term_of(d_ts->get_initial_states());
  const expr::term& invar = tm().term_of(d_sf->get_formula());

  expr::term::expr_let_cache let_cache;
  std::vector<expr::term_ref> definitions;
  trans.mk_let_cache(tm(), let_cache, definitions);
  init.mk_let_cache(tm(), let_cache, definitions);
  invar.mk_let_cache(tm(), let_cache, definitions);

  if (definitions.size()) {
    out << "DEFINE" << std::endl;
    for (size_t i = 0; i < definitions.size(); ++ i) {
      expr::term::expr_let_cache::const_iterator find = let_cache.find(definitions[i]);
      assert(find != let_cache.end());
      out << "    " << find->second << " := ";
      tm().term_of(definitions[i]).to_stream_nuxmv_without_let(out, tm(), let_cache, false);
      out << ";" << std::endl;
    }
  }
  out << std::endl;

  // The transition relation
  out << "TRANS" << std::endl;
  out << "    ";
  trans.to_stream_nuxmv_without_let(out, tm(), let_cache);
  out << ";" << std::endl;
  out << std::endl;

  // The initial state
  st->use_namespace(system::state_type::STATE_CURRENT);
  out << "INIT" << std::endl;
  out << "    ";
  init.to_stream_nuxmv_without_let(out, tm(), let_cache);
  out << ";" << std::endl;
  out << std::endl;
  ctx().tm().pop_namespace();

  // Output the query
  st->use_namespace(system::state_type::STATE_CURRENT);
  out << "INVARSPEC" << std::endl;
  out << "    ";
  invar.to_stream_nuxmv_without_let(out, tm(), let_cache);
  out << ";" << std::endl;
  ctx().tm().pop_namespace();

  // State type namespace
  ctx().tm().pop_namespace();

  // Name transformer reset
  delete name_transformer;
  tm().set_name_transformer(0);
}

static inline
bool isalnum_not(char c) { return !isalnum(c); }

static inline
std::string escape_var_name(std::string name) {
  if (find_if(name.begin(), name.end(), isalnum_not) != name.end()) {
    name = "|" + name + "|";
  }
  return name;
}

void translator::to_stream_horn(std::ostream& out) const {
  // The state type
  const system::state_type* state_type = d_ts->get_state_type();

  // Use the state type namespace
  state_type->use_namespace();

  // Collect the state variables into these streams
  std::stringstream state_vars;
  std::stringstream next_vars;
  std::stringstream quant_vars_trans;
  std::stringstream quant_vars_state;

  quant_vars_trans << expr::set_output_language(output::HORN);
  quant_vars_trans << expr::set_tm(ctx().tm());
  quant_vars_state << expr::set_output_language(output::HORN);
  quant_vars_state << expr::set_tm(ctx().tm());

  out << "(set-logic HORN)" << std::endl;

  // The invariant we're looking for
  out << "(declare-fun invariant (";
  const expr::term& state_type_term = tm().term_of(state_type->get_state_type_var());
  size_t state_type_size = tm().get_struct_type_size(state_type_term);
  for (size_t i = 0; i < state_type_size; ++ i) {
    std::string id = tm().get_struct_type_field_id(state_type_term, i);
    expr::term_ref type = tm().get_struct_type_field_type(state_type_term, i);
    std::string state_id = escape_var_name("state." + id);
    std::string next_id = escape_var_name("next." + id);
    if (i) {
      out << " ";
      state_vars << " ";
      next_vars << " ";
      quant_vars_trans << " ";
      quant_vars_state << " ";
    }
    out << type;
    state_vars << state_id;
    next_vars << next_id;
    quant_vars_trans << "(" << state_id << " " << type << ")";
    quant_vars_state << "(" << state_id << " " << type << ")";
    quant_vars_trans << " (" << next_id << " " << type << ")";
  }
  out << ") Bool)" << std::endl;
  out << std::endl;

  // The initial state
  expr::term_ref I = d_ts->get_initial_states();
  out << ";; Initial state" << std::endl;
  out << "(assert" << std::endl;
  out << "  (forall (" << quant_vars_state.str() << ")" << std::endl;
  out << "    (=> " << I << std::endl;
  out << "        (invariant " << state_vars.str() << "))" << std::endl;
  out << "  )" << std::endl;
  out << ")" << std::endl;
  out << std::endl;

  // Add input vars to the transition quant
  const expr::term& input_type_term = tm().term_of(state_type->get_input_type_var());
  size_t input_type_size = tm().get_struct_type_size(input_type_term);
  for (size_t i = 0; i < input_type_size; ++ i) {
    std::string id = tm().get_struct_type_field_id(input_type_term, i);
    expr::term_ref type = tm().get_struct_type_field_type(input_type_term, i);
    quant_vars_trans << " ";
    quant_vars_trans << "(input." << id << " " << type << ")";
  }

  // The transition relation
  expr::term_ref T = d_ts->get_transition_relation();
  out << ";; Transition relation" << std::endl;
  out << "(assert" << std::endl;
  out << "  (forall (" << quant_vars_trans.str() << ")" << std::endl;
  out << "    (=> (and (invariant " << state_vars.str() << ")" << std::endl;
  out << "             " << T << std::endl;
  out << "        )" << std::endl;
  out << "        (invariant " << next_vars.str() << ")" << std::endl;
  out << "    )" << std::endl;
  out << "  )" << std::endl;
  out << ")" << std::endl;
  out << std::endl;

  // The query
  expr::term_ref Q = d_sf->get_formula();
  out << ";; Property" << std::endl;
  out << "(assert" << std::endl;
  out << "  (forall (" << quant_vars_state.str() << ")" << std::endl;
  out << "    (=> (invariant " << state_vars.str() << ")" << std::endl;
  out << "        " << Q << std::endl;
  out << "    )" << std::endl;
  out << "  )" << std::endl;
  out << ")" << std::endl;
  out << std::endl;

  out << ";; Check the property" << std::endl;
  out << "(check-sat)" << std::endl;

  // State type namespace
  ctx().tm().pop_namespace();
}

engine::result translator::query(const system::transition_system* ts, const system::state_formula* sf) {

  d_ts = ts;
  d_sf = sf;

  language lang = output::get_output_language(std::cout);

  switch (lang) {
  case MCMT:
    to_stream_mcmt(std::cout);
    break;
  case NUXMV:
    to_stream_nuxmv(std::cout);
    break;
  case HORN:
    to_stream_horn(std::cout);
    break;
  default:
    throw exception("Unsupported translation language");
  }

  return SILENT;
}

const system::trace_helper* translator::get_trace() {
  throw exception("Not supported.");
}

engine::invariant translator::get_invariant() {
  throw exception("Not supported.");
}

}
}
