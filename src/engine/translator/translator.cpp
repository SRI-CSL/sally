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
  out << "(define-state-type state_type " << state_type->get_type() << ")" << std::endl;
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

class lustre_transition_name_transformer : public utils::name_transformer {
public:
  std::string apply(std::string id) const {
    // state.x => x
    if (6 < id.size() && id.substr(0, 6) == "state.") {
      id = std::string("pre(") + id.substr(6) + std::string(")");
    } else
    // next.x => xx_next
    if (5 < id.size() && id.substr(0, 5) == "next.") {
      id = id.substr(5) + std::string("_next");
    }
    // Replace any bad characters
    std::replace(id.begin(), id.end(), '!', '_');
    return id;
  }
};

class lustre_initial_name_transformer : public utils::name_transformer {
public:
  std::string apply(std::string id) const {
    // state.x => x
    if (6 < id.size() && id.substr(0, 6) == "state.") {
      id = id.substr(6) + std::string("_init");
    }
    // Replace any bad characters
    std::replace(id.begin(), id.end(), '!', '_');
    return id;
  }
};


void translator::to_stream_lustre(std::ostream& out) const {

  lustre_initial_name_transformer init_transformer;
  lustre_transition_name_transformer transition_transformer;

  // The state type
  const system::state_type* state_type = d_ts->get_state_type();
  state_type->use_namespace();

  // Get the variables
  const expr::term& state_type_term = tm().term_of(state_type->get_type());
  size_t state_type_size = tm().get_struct_type_size(state_type_term);
  std::vector<std::string> vars;
  std::vector<expr::term_ref> types;
  for (size_t i = 0; i < state_type_size; ++ i) {
    std::string id = tm().get_struct_type_field_id(state_type_term, i);
    id = init_transformer.apply(id);
    vars.push_back(id);
    types.push_back(tm().get_struct_type_field_type(state_type_term, i));
  }

  // Main node start
  out << "node main (";
  for (size_t i = 0; i < state_type_size; ++ i) {
    if (i) { out << "; "; }
    out << vars[i] << "_init : " << types[i] << "; ";
    out << vars[i] << "_next : " << types[i];
  }
  out << ") returns (OK: bool);" << std::endl;

  // Local state variables
  out << "  var";
  for (size_t i = 0; i < state_type_size; ++ i) {
    out << " " << vars[i] << " : " << types[i] << ";";
  }
  out << std::endl;

  // Start the node definition
  out << "let" << std::endl;

  // Initial state
  tm().set_name_transformer(&init_transformer);
  out << "  --Initial condition" << std::endl;
  out << "  assert(" << d_ts->get_initial_states() << ");" << std::endl;
  out << std::endl;
  tm().set_name_transformer(0);

  // Transition relation
  tm().set_name_transformer(&transition_transformer);
  out << "  --Transition relation" << std::endl;
  out << "  assert(true -> " << d_ts->get_transition_relation() << ");" << std::endl;
  out << std::endl;
  tm().set_name_transformer(0);

  // Assign variable to their next values
  out << "  --Assign to next" << std::endl;
  for (size_t i = 0; i < state_type_size; ++ i) {
    out << "  " << vars[i] << " = " << vars[i] << "_init -> " << vars[i] << "_next;" << std::endl;
  }
  out << std::endl;

  // The property
  state_type->use_namespace(system::state_type::STATE_CURRENT);
  tm().set_name_transformer(&transition_transformer);
  out << "  --The property" << std::endl;
  out << "  OK = " << d_sf->get_formula() << ";" << std::endl;
  tm().set_name_transformer(0);
  ctx().tm().pop_namespace();

  // Finish
  out << "  --%PROPERTY OK;" << std::endl;
  out << "tel" << std::endl;

  // State type namespace
  ctx().tm().pop_namespace();
}


void translator::to_stream_horn(std::ostream& out) const {
  // The state type
  const system::state_type* state_type = d_ts->get_state_type();

  // Use the state type namespace
  state_type->use_namespace();

  // Collect the state variables into these streams
  std::stringstream state_vars;
  std::stringstream next_vars;
  std::stringstream quant_vars;

  quant_vars << expr::set_output_language(output::HORN);
  quant_vars << expr::set_tm(ctx().tm());

  out << "(set-logic HORN)" << std::endl;

  // The invariant we're looking for
  out << "(declare-fun invariant (";
  const expr::term& state_type_term = tm().term_of(state_type->get_type());
  size_t state_type_size = tm().get_struct_type_size(state_type_term);
  for (size_t i = 0; i < state_type_size; ++ i) {
    std::string id = tm().get_struct_type_field_id(state_type_term, i);
    expr::term_ref type = tm().get_struct_type_field_type(state_type_term, i);
    if (i) {
      out << " ";
      state_vars << " ";
      next_vars << " ";
      quant_vars << " ";
    }
    out << type;
    state_vars << "state." << id;
    next_vars << "next." << id;
    quant_vars << "(state." << id << " " << type << ")";
    quant_vars << " (next." << id << " " << type << ")";
  }
  out << ") Bool)" << std::endl;
  out << std::endl;

  // The initial state
  expr::term_ref I = d_ts->get_initial_states();
  out << ";; Initial state" << std::endl;
  out << "(assert" << std::endl;
  out << "  (forall (" << quant_vars.str() << ")" << std::endl;
  out << "    (=> " << I << std::endl;
  out << "        (invariant " << state_vars.str() << "))" << std::endl;
  out << "  )" << std::endl;
  out << ")" << std::endl;
  out << std::endl;

  // The transition relation
  expr::term_ref T = d_ts->get_transition_relation();
  out << ";; Transition relation state" << std::endl;
  out << "(assert" << std::endl;
  out << "  (forall (" << quant_vars.str() << ")" << std::endl;
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
  out << "  (forall (" << quant_vars.str() << ")" << std::endl;
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
  case LUSTRE:
    to_stream_lustre(std::cout);
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
