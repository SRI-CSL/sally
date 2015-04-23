/*
 * solvers.h
 *
 *  Created on: Apr 22, 2015
 *      Author: dejan
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

  /** Rewrite equalitites to inequalities */
  expr::term_ref eq_to_ineq(expr::term_ref G);

  /** Get the enabling varibale of frame k */
  expr::term_ref get_frame_variable(size_t k);

  /** Returns the induction solver */
  smt::solver* get_induction_solver();

  /** Returns the unique reachability solver */
  smt::solver* get_reachability_solver();

  /** Returns the k-th reachability solver */
  smt::solver* get_reachability_solver(size_t k);

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

  /** Checks formula f for satisfiability at frame k using the reachability solvers and returns the generalization. */
  expr::term_ref query_at(size_t k, expr::term_ref f, smt::solver::formula_class f_class);

  /** Check if f is inductive */
  expr::term_ref check_inductive(expr::term_ref f);

  /** Learn forward to refute G at k from k-1 using reachability solvers */
  expr::term_ref learn_forward(size_t k, expr::term_ref G);

  /** Returns the counterexample solver */
  smt::solver* get_counterexample_solver();

  /** Make sure that the counter-example solver has frames 0, ..., k */
  void ensure_counterexample_solver_depth(size_t k);

  /** Make sure that the counter-example knows about variables in frames 0, .., k-1 */
  void ensure_counterexample_solver_variables(size_t k);

  /** Collect solver garbage */
  void gc();

  /** Collect term manager garbage */
  void gc_collect(const expr::gc_relocator& gc_reloc);

};


}
}
