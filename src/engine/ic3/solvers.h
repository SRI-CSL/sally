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

#include <set>
#include <vector>

#include "smt/solver.h"
#include "expr/term_manager.h"
#include "expr/gc_relocator.h"
#include "system/transition_system.h"
#include "system/state_trace.h"
#include "system/context.h"

namespace sally {
namespace ic3 {

/**
 * Class to manage solvers in IC3.
 *
 * There are three dedicated solver available:
 *   [Reachability] Solver(s) to check one-step reachability from frame to
 *                  next frame. These can be a single solver that uses boolean
 *                  variables to select the frame in question. Checks here should
 *                  only be done through query_at method.
 *   [Induction]    Solver to check induction from last frame. Checks here should
 *                  only be done through the check_inductive method.
 *   [Counterexample] Solver for BMC checks.
 */
class solvers {

  typedef std::set<expr::term_ref> formula_set;

  /** Context */
  const system::context& d_ctx;

  /** Term manager */
  expr::term_manager& d_tm;

  /** Transition system for these solvers */
  const system::transition_system* d_transition_system;

  /** Number of frames */
  size_t d_size;

  /** The trace to get the state variables for unrolling */
  system::state_trace* d_trace;

  /** A solver per frame with transition relation info */
  std::vector<smt::solver*> d_reachability_solvers;

  /** Solver for reachability queries when in single-solver mode */
  smt::solver* d_reachability_solver;

  /** Solver for induction queries when in single-solver mode */
  smt::solver* d_induction_solver;

  /** Counter-example solver */
  smt::solver* d_counterexample_solver;

  /** Number of transition releations asserted to counterexample solver */
  size_t d_counterexample_solver_depth;

  /** One past the frame number where variables are known to the solver */
  size_t d_counterexample_solver_variables_depth;

  /** Boolean variable (enabling the frame) */
  std::vector<expr::term_ref> d_frame_variables;

  /** Initialize the reachability solver for frame k */
  void init_reachability_solver(size_t k);

  /** Generalize the SAT result at k */
  expr::term_ref generalize_sat(smt::solver* solver);

  /** Get the enabling varibale of frame k */
  expr::term_ref get_frame_variable(size_t k);

  /** Returns the induction solver */
  smt::solver* get_induction_solver();

  /** Returns the unique reachability solver */
  smt::solver* get_reachability_solver();

  /** Returns the k-th reachability solver */
  smt::solver* get_reachability_solver(size_t k);

  /** Notify class to reset the cex solver to its previous depth */
  class cex_destruct_notify : public smt::solver_scope::destructor_notify {
    solvers* d_solvers;
    size_t d_depth;
  public:
    cex_destruct_notify(solvers* s)
    : d_solvers(s)
    , d_depth(s->get_counterexample_solver_depth())
    {}
    ~cex_destruct_notify() {
      d_solvers->d_counterexample_solver_depth = d_depth;
    }
  };

  /** Returns the counterexample solver */
  smt::solver* get_counterexample_solver();

  /** Assert frame selection variables */
  void assert_frame_selection(size_t k, smt::solver* solver);

  /** Whether to generate models for queries */
  bool d_generate_models_for_queries;

public:

  /** Create solvers for the given transition system */
  solvers(const system::context& ctx, const system::transition_system* transition_system, system::state_trace* trace);

  /** Delete the solvers */
  ~solvers();

  /** Mark a new frame */
  void new_frame();

  /** Get number of frames */
  size_t size();

  /** Reset all the solvers. */
  void reset(const std::vector<formula_set>& frames);

  /** Add a formula to frame k */
  void add(size_t k, expr::term_ref f);

  struct query_result {
    /** Result of the query */
    smt::solver::result result;
    /** Model, if sat */
    expr::model::ref model;
    /** The generalization, if sat */
    expr::term_ref generalization;

    query_result();
  };

  /** Checks formula f for satisfiability at frame k using the reachability solvers and returns the generalization. */
  query_result query_at(size_t k, expr::term_ref f, smt::solver::formula_class f_class);

  /** Check if f is inductive */
  query_result check_inductive(expr::term_ref f);

  /** Learn forward to refute G at k from k-1 using reachability solvers */
  expr::term_ref learn_forward(size_t k, expr::term_ref G);

  /** Returns the counterexample solver */
  void get_counterexample_solver(smt::solver_scope& solver);

  /** Returns the depth of the counterexample solver */
  size_t get_counterexample_solver_depth() const;

  /** Make sure that the counter-example solver has frames 0, ..., k */
  void ensure_counterexample_solver_depth(size_t k);

  /** Whether to return models with queries */
  void generate_models_for_queries(bool flag);

  /** Collect solver garbage */
  void gc();

  /** Collect term manager garbage */
  void gc_collect(const expr::gc_relocator& gc_reloc);

  /** Rewrite equalitites to inequalities */
  expr::term_ref eq_to_ineq(expr::term_ref G);
};


}
}
