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

#include <vector>
#include <iosfwd>

namespace sally {
namespace system {

class state_trace : public expr::gc_participant {

  /** The state type */
  const state_type* d_state_type;

  /** Sequence of state variables, per frame */
  std::vector<expr::term_ref_strong> d_state_variables;

  /** Sequence of input variables, per step */
  std::vector<expr::term_ref_strong> d_input_variables;

  /** Full model of the trace */
  expr::model d_model;

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

public:

  /** Create ta trace for the given type */
  state_trace(const state_type* st);

  /** Get the size of the trace */
  size_t size() const;

  /**
   * Get the state variables at k.
   */
  void get_state_variables(size_t k, std::vector<expr::term_ref>& vars);

  /**
   * Get the input variables at k.
   */
  void get_input_variables(size_t k, std::vector<expr::term_ref>& vars);

  /**
   * Given a formula in the state type return a state formula in the k-th step.
   */
  expr::term_ref get_state_formula(expr::term_ref sf, size_t k);

  /**
   * Given a transition formula in the state type return a transition formula
   * from k to k + 1 step.
   */
  expr::term_ref get_transition_formula(expr::term_ref tf, size_t k);

  /**
   * Add model to the trace (model over trace variables).
   */
  void add_model(const expr::model& m);

  /**
   * Output the trace to the stream.
   */
  void to_stream(std::ostream& out) const;

  /** Resize trace to 0 .. size -1 */
  void resize_to(size_t size);

  /** Collect the terms */
  void gc_collect(const expr::gc_relocator& gc_reloc);

};

std::ostream& operator << (std::ostream& out, const state_trace& trace);

}
}
