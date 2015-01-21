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

  /** Output the state type */
  const system::state_type* state_type = d_ts->get_state_type();
  state_type->use_namespace();
  out << ";; State type" << std::endl;
  out << "(declare-state-type state_type " << state_type->get_type() << ")" << std::endl;
  out << std::endl;

  /** Output the initial state */
  state_type->use_namespace(system::state_type::STATE_CURRENT);
  expr::term_ref initial_states = d_ts->get_initial_states();
  out << ";; Initial states" << std::endl;
  out << "(define-states initial_states state_type " << initial_states << ")" << std::endl;
  out << std::endl;
  ctx().tm().pop_namespace();

  /** Output the transition relation */
  expr::term_ref transition_relation = d_ts->get_transition_relation();
  out << ";; Transition relation" << std::endl;
  out << "(define-transition transition state_type " << transition_relation << ")" << std::endl;
  out << std::endl;

  /** Output the transition system */
  out << ";; Transition system" << std::endl;
  out << "(define-transition-system T state_type initial_states (transition))" << std::endl;
  out << std::endl;

  /** Output any assumptions */
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

  /** Output the query */
  state_type->use_namespace(system::state_type::STATE_CURRENT);
  out << ";; Query " << std::endl;
  out << "(query T " << d_sf->get_formula() << std::endl;
  ctx().tm().pop_namespace();

  // State type namespace
  ctx().tm().pop_namespace();
}

void translator::to_stream_nuxmv(std::ostream& out) {

}

void translator::to_stream_horn(std::ostream& out) {

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
