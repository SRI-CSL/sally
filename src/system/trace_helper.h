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

#pragma once

#include "expr/model.h"
#include "expr/gc_participant.h"
#include "system/state_type.h"
#include "smt/solver.h"

#include <vector>
#include <iosfwd>

namespace sally {
namespace system {

/**
 * Trace helper is a helper class for construcing traces. A trace
 * helper can be obtained from the transition system. With a trace
 * helper one can attach useful information to a trace. The simplest
 * example is constructing a counter-example, where the user of
 * the helper can attach models to frames of the trace.
 */
class trace_helper : public expr::gc_participant {

  /** The state type */
  const state_type* d_state_type;

  /** Sequence of state variables structs, per frame */
  std::vector<expr::term_ref_strong> d_state_variables_structs;

  /** Sequence of state variables sets, per frame */
  std::vector< std::vector<expr::term_ref> > d_state_variables;

  /** Sequence of input variables, per step */
  std::vector<expr::term_ref_strong> d_input_variables_structs;

  /** Sequence of input variables sets, per frame */
  std::vector< std::vector<expr::term_ref> > d_input_variables;

  /** Renaming from state variable to frame variables */
  std::vector<expr::term_manager::substitution_map> d_subst_maps_state_to_trace;

  /** Renaming from frame variables to state variables */
  std::vector<expr::term_manager::substitution_map> d_subst_maps_trace_to_state;

  /** Full model of the trace */
  expr::model::ref d_model;

  /** Size of the model */
  size_t d_model_size;

  /** Ensure variables up to (and including) frame k */
  void ensure_variables(size_t k);

  /**
   * Get the variables in the given struct
   */
  void get_struct_variables(expr::term_ref s, std::vector<expr::term_ref>& out) const;

  /** Returns the state variables for frame k */
  expr::term_ref get_state_struct_variable(size_t k);

  /** Retruns the input variables for frame k */
  expr::term_ref get_input_struct_variable(size_t k);

  /** Returns the term manager */
  expr::term_manager& tm() const;

  /**
   * Create a trace for the given type (only transition system can create one.
   * Others use the helper provided by the transition system.
   */
  trace_helper(const state_type* st);

  /** Same for destructor, only transition system can use it */
  virtual ~trace_helper() {}

  friend class transition_system;

  /** Make an equality x = v, where v is the value of x in the model */
  expr::term_ref mk_equality(expr::term_ref x, expr::model::ref m);

  /** To stream with regular MCMT language */
  void to_stream_mcmt(std::ostream& out) const;

  /** To stream using CSV */
  void to_stream_tab(std::ostream& out) const;

public:

  /** Get the size of the trace */
  size_t size() const;

  /** Clear the trace helper (remove all model information) */
  void clear_model();

  /**
   * Get the state variables at k.
   */
  const std::vector<expr::term_ref>& get_state_variables(size_t k);

  /**
   * Get the input variables at k.
   */
  const std::vector<expr::term_ref>& get_input_variables(size_t k);

  /**
   * Given a formula in the state type, return a state formula in the k-th step.
   */
  expr::term_ref get_state_formula(expr::term_ref sf, size_t k);

  /**
   * Given a state formula in the k-th step, return a formula in the state type
   */
  expr::term_ref get_state_formula(size_t k, expr::term_ref sf);

  /**
   * Given a transition formula in the state type return a transition formula
   * from k to k + 1 step.
   */
  expr::term_ref get_transition_formula(expr::term_ref tf, size_t k);

  /**
   * Returns the model associated with the trace.
   */
  expr::model::ref get_model() const;

  /** 
   * Adds a part of the given model to the solver as assertions. The part that 
   * is asserted are the variables for frames start, ..., end. 
   */
  void add_model_to_solver(expr::model::ref m, size_t start, size_t end, smt::solver* solver, smt::solver::formula_class c);

  /**
   * Add model to the trace (model over trace variables), for frames
   * start, ..., end. All other model variables will not be added.
   */
  void set_model(expr::model::ref m, size_t start, size_t end);

  /**
   * Check if formula is false in given frame.
   */
  bool is_true_in_frame(size_t frame, expr::term_ref f, expr::model::ref model);

  /**
   * Check if formula is true in given frame.
   */
  bool is_false_in_frame(size_t frame, expr::term_ref f, expr::model::ref model);

  /**
   * Output the trace to the stream.
   */
  void to_stream(std::ostream& out) const;

  /** Collect the terms */
  void gc_collect(const expr::gc_relocator& gc_reloc);

};

std::ostream& operator << (std::ostream& out, const trace_helper& trace);

}
}
