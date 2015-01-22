/*
 * translator.cpp
 *
 *  Created on: Jan 20, 2015
 *      Author: dejan
 */

#include "engine/translator/translator.h"

#include "smt/factory.h"
#include "utils/output.h"

#include <sstream>
#include <iostream>
#include <algorithm>

namespace sal2 {
namespace output {

translator::translator(const system::context& ctx)
: engine(ctx)
, d_ts(0)
, d_sf(0)
{
}

translator::~translator() {
}

void translator::to_stream_mcmt(std::ostream& out) {

  // Output the state type
  const system::state_type* state_type = d_ts->get_state_type();
  state_type->use_namespace();
  out << ";; State type" << std::endl;
  out << "(declare-state-type state_type " << state_type->get_type() << ")" << std::endl;
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
  out << "(define-transition-system T state_type initial_states (transition))" << std::endl;
  out << std::endl;

  // Output any assumptions
  if (d_ts->has_assumptions()) {
    state_type->use_namespace(system::state_type::STATE_CURRENT);
    const std::vector<system::state_formula*>& assumptions = d_ts->get_assumptions();
    for (size_t i = 0; i < assumptions.size(); ++ i) {
      out << ";; Assumption " << std::endl;
      out << "(assume T " << assumptions[i]->get_formula() << ")" << std::endl;
      out << std::endl;
    }
    ctx().tm().pop_namespace();
  }

  // Output the query
  state_type->use_namespace(system::state_type::STATE_CURRENT);
  out << ";; Query " << std::endl;
  out << "(query T " << d_sf->get_formula() << std::endl;
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
    // next.x => next(x)
    if (5 < id.size() && id.substr(0, 5) == "next.") {
      id = std::string("next(") + id.substr(5) + std::string(")");
    }
    // Replace any bad characters
    std::replace(id.begin(), id.end(), '!', '_');
    return id;
  }
};

void translator::to_stream_nuxmv(std::ostream& out) {

  // Name transformer
  nuxmv_name_transformer* name_transformer = new nuxmv_name_transformer();
  tm().set_name_transformer(name_transformer);

  // The state type
  const system::state_type* state_type = d_ts->get_state_type();
  state_type->use_namespace();

  out << "MODULE main" << std::endl;

  // Declare state variables
  out << "VAR" << std::endl;
  const expr::term& state_type_term = tm().term_of(state_type->get_type());
  size_t state_type_size = tm().get_struct_type_size(state_type_term);
  for (size_t i = 0; i < state_type_size; ++ i) {
    std::string var_name = name_transformer->apply(tm().get_struct_type_field_id(state_type_term, i));
    out << "    " << var_name << ": " << tm().get_struct_type_field_type(state_type_term, i) << ";" << std::endl;
  }
  out << std::endl;

  // The transition relation
  out << "TRANS" << std::endl;
  out << "    " << d_ts->get_transition_relation() << ";" << std::endl;
  out << std::endl;

  // The initial state
  state_type->use_namespace(system::state_type::STATE_CURRENT);
  out << "INIT" << std::endl;
  out << "    " << d_ts->get_initial_states() << ";" << std::endl;
  out << std::endl;
  ctx().tm().pop_namespace();

  // Output the query
  state_type->use_namespace(system::state_type::STATE_CURRENT);
  out << "INVARSPEC" << std::endl;
  out << "    " << d_sf->get_formula() << ";" << std::endl;
  ctx().tm().pop_namespace();

  // State type namespace
  ctx().tm().pop_namespace();

  // Name transformer reset
  delete name_transformer;
  tm().set_name_transformer(0);
}

void translator::to_stream_horn(std::ostream& out) {
  // The state type
  const system::state_type* state_type = d_ts->get_state_type();

  // Use the state type namespace
  state_type->use_namespace();

  // Collect the state variables into these streams
  std::stringstream state_vars;
  std::stringstream next_vars;

  // The invariant we're looking for
  out << "(declare-rel invariant (";
  const expr::term& state_type_term = tm().term_of(state_type->get_type());
  size_t state_type_size = tm().get_struct_type_size(state_type_term);
  for (size_t i = 0; i < state_type_size; ++ i) {
    if (i) { out << " "; state_vars << " "; next_vars << " "; }
    out << tm().get_struct_type_field_type(state_type_term, i);
    state_vars << "state." << tm().get_struct_type_field_id(state_type_term, i);
    next_vars << "next." << tm().get_struct_type_field_id(state_type_term, i);
  }
  out << "))" << std::endl;
  out << std::endl;

  // Declare state and next variables
  for (size_t i = 0; i < state_type_size; ++ i) {
    out << "(declare-var " << "state." << tm().get_struct_type_field_id(state_type_term, i) << " " << tm().get_struct_type_field_type(state_type_term, i) << ")" << std::endl;
    out << "(declare-var " << "next." << tm().get_struct_type_field_id(state_type_term, i) << " " << tm().get_struct_type_field_type(state_type_term, i) << ")" << std::endl;
  }
  out << std::endl;

  // The initial state
  expr::term_ref I = d_ts->get_initial_states();
  out << "(rule (=> " << I << "(invariant " << state_vars.str() << ")))" << std::endl;

  // The transition relation
  expr::term_ref T = d_ts->get_transition_relation();
  out << "(rule (=> (and (invariant " << state_vars.str() << ") " << T << ") (invariant " << next_vars.str() << ")))" << std::endl;

  // The query
  out << std::endl;
  expr::term_ref Q = d_sf->get_formula();
  out << "(query (and (invariant " << state_vars.str() << ") (not " << Q << ")))" << std::endl;

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
    throw exception("Unsupported language");
  }

  return SILENT;
}

const system::state_trace* translator::get_trace() {
  throw exception("Not supported.");
}

}
}
