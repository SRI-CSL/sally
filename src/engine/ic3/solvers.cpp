/*
 * ic3_engine_solvers.cpp
 *
 *  Created on: Apr 22, 2015
 *      Author: dejan
 */

#include "engine/ic3/solvers.h"

#include "smt/factory.h"
#include "utils/trace.h"


#include <iostream>

#define unused_var(x) { (void)x; }

namespace sally {
namespace ic3 {

solvers::solvers(const system::context& ctx, const system::transition_system* transition_system, system::state_trace* trace)
: d_ctx(ctx)
, d_tm(ctx.tm())
, d_transition_system(transition_system)
, d_size(0)
, d_trace(trace)
, d_reachability_solver(0)
, d_induction_solver(0)
, d_counterexample_solver(0)
, d_counterexample_solver_depth(0)
, d_counterexample_solver_variables_depth(0)
{
}

solvers::~solvers() {
  delete d_reachability_solver;
  delete d_induction_solver;
  delete d_counterexample_solver;
  for (size_t k = 0; k < d_reachability_solvers.size(); ++ k) {
    delete d_reachability_solvers[k];
  }
}

void solvers::reset(const std::vector<solvers::formula_set>& frames) {

  MSG(1) << "ic3: restarting solvers" << std::endl;

  if (!d_ctx.get_options().get_bool("ic3-single-solver")) {
    // Restart the solver
    assert(d_size == d_reachability_solvers.size());
    assert(d_size == frames.size());
    for (size_t k = 0; k < d_size; ++ k) {
      delete d_reachability_solvers[k];
      d_reachability_solvers[k] = 0;
    }
  } else {
    // Restart the reachability solver
    delete d_reachability_solver;
    d_reachability_solver = 0;
  }

  // Add the frame content
  for (size_t k = 0; k < frames.size(); ++ k) {
    // Add the content again
    formula_set::const_iterator it = frames[k].begin();
    for (; it != frames[k].end(); ++ it) {
      add(k, *it);
    }
  }

  // Clear the induction solver
  delete d_induction_solver;
  d_induction_solver = 0;

  // Reset the counterexample solver
  delete d_counterexample_solver;
  d_counterexample_solver = 0;
  ensure_counterexample_solver_depth(d_size);
}

void solvers::init_reachability_solver(size_t k) {

  assert(!d_ctx.get_options().get_bool("ic3-single-solver"));
  assert(k < d_size);

  // The variables from the state types
  const std::vector<expr::term_ref>& x = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_CURRENT);
  const std::vector<expr::term_ref>& x_next = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_NEXT);

  // A solver per frame
  while (d_reachability_solvers.size() <= k) {
    smt::solver* solver = smt::factory::mk_default_solver(d_tm, d_ctx.get_options());
    d_reachability_solvers.push_back(solver);
    solver->add_variables(x.begin(), x.end(), smt::solver::CLASS_A);
    solver->add_variables(x_next.begin(), x_next.end(), smt::solver::CLASS_B);
    solver->add(d_transition_system->get_transition_relation(), smt::solver::CLASS_T);
  }
}

void solvers::ensure_counterexample_solver_depth(size_t k) {
  // Make sure we unrolled the solver up to k
  for (; d_counterexample_solver_depth < k; ++ d_counterexample_solver_depth) {
    // Add transition relation k -> k + 1 to the counter-example solver
    expr::term_ref T = d_trace->get_transition_formula(d_transition_system->get_transition_relation(), d_counterexample_solver_depth, d_counterexample_solver_depth + 1);
    get_counterexample_solver()->add(T, smt::solver::CLASS_T);
  }
}

void solvers::ensure_counterexample_solver_variables(size_t k) {
  // Make sure we unrolled the solver up to k
  for (; d_counterexample_solver_variables_depth <= k; ++ d_counterexample_solver_variables_depth) {
    // Add variables
    std::vector<expr::term_ref> variables;
    d_trace->get_state_variables(d_counterexample_solver_variables_depth, variables);
    get_counterexample_solver()->add_variables(variables.begin(), variables.end(), smt::solver::CLASS_A);
  }
}

smt::solver* solvers::get_induction_solver() {
  if (d_induction_solver == 0) {
    // The variables from the state types
    const std::vector<expr::term_ref>& x = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_CURRENT);
    const std::vector<expr::term_ref>& x_next = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_NEXT);
    // Make the solver
    d_induction_solver = smt::factory::mk_default_solver(d_tm, d_ctx.get_options());
    d_induction_solver->add(d_transition_system->get_transition_relation(), smt::solver::CLASS_T);
    d_induction_solver->add_variables(x.begin(), x.end(), smt::solver::CLASS_A);
    d_induction_solver->add_variables(x_next.begin(), x_next.end(), smt::solver::CLASS_B);
  }
  return d_induction_solver;
}

smt::solver* solvers::get_reachability_solver() {
  assert(d_ctx.get_options().get_bool("ic3-single-solver"));
  if (d_reachability_solver == 0) {
    // The variables from the state types
    const std::vector<expr::term_ref>& x = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_CURRENT);
    const std::vector<expr::term_ref>& x_next = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_NEXT);
    // Make the solver
    d_reachability_solver = smt::factory::mk_default_solver(d_tm, d_ctx.get_options());
    d_reachability_solver->add(d_transition_system->get_transition_relation(), smt::solver::CLASS_T);
    d_reachability_solver->add_variables(x.begin(), x.end(), smt::solver::CLASS_A);
    d_reachability_solver->add_variables(x_next.begin(), x_next.end(), smt::solver::CLASS_B);
  }
  return d_reachability_solver;
}

smt::solver* solvers::get_reachability_solver(size_t k) {
  assert(!d_ctx.get_options().get_bool("ic3-single-solver"));
  init_reachability_solver(k);
  return d_reachability_solvers[k];
}

smt::solver* solvers::get_counterexample_solver() {
  if (d_counterexample_solver == 0) {
    // Make the solver
    d_counterexample_solver = smt::factory::mk_default_solver(d_tm, d_ctx.get_options());
    // Add the initial state
    expr::term_ref I0 = d_trace->get_state_formula(d_transition_system->get_initial_states(), 0);
    d_counterexample_solver->add(I0, smt::solver::CLASS_A);
    // Set the depth
    d_counterexample_solver_depth = 0;
    d_counterexample_solver_variables_depth = 0;
  }
  return d_counterexample_solver;
}

void solvers::get_counterexample_solver(smt::solver_scope& solver) {
  solver.set_solver(get_counterexample_solver());
  solver.set_destructor_notify(new cex_destruct_notify(this));
}

size_t solvers::get_counterexample_solver_depth() const {
  return d_counterexample_solver_depth;

}

void solvers::gc() {
  for (size_t i = 0; i < d_reachability_solvers.size(); ++ i) {
    if (d_reachability_solvers[i]) {
      d_reachability_solvers[i]->gc();
    }
  }
  if (d_counterexample_solver) {
    d_counterexample_solver->gc();
  }
  if (d_induction_solver) {
    d_induction_solver->gc();
  }
  if (d_reachability_solver) {
    d_reachability_solver->gc();
  }
}

void solvers::assert_frame_selection(size_t k, smt::solver* solver) {
  bool frame_selected = false;
  for (size_t i = 0; i < d_size; ++ i) {
    expr::term_ref frame_variable = get_frame_variable(i);
    if (i == k) {
      solver->add(frame_variable, smt::solver::CLASS_A);
      frame_selected = true;
    } else {
      solver->add(d_tm.mk_term(expr::TERM_NOT, frame_variable), smt::solver::CLASS_A);
    }
  }
  assert(frame_selected);
}

expr::term_ref solvers::query_at(size_t k, expr::term_ref f, smt::solver::formula_class f_class) {

  smt::solver* solver = 0;

  if (d_ctx.get_options().get_bool("ic3-single-solver")) {
    solver = get_reachability_solver();
  } else {
    solver = get_reachability_solver(k);
  }
  smt::solver_scope scope(solver);

  // Add the formula (moving current -> next)
  scope.push();
  solver->add(f, f_class);

  // Add frame selection if needed
  if (d_ctx.get_options().get_bool("ic3-single-solver")) {
    assert_frame_selection(k, solver);
  }

  // Figure out the result
  smt::solver::result r = solver->check();
  switch (r) {
  case smt::solver::SAT: {
    return generalize_sat(solver);
  }
  case smt::solver::UNSAT:
    // Unsat, we return NULL
    return expr::term_ref();
  default:
    throw exception("SMT unknown result.");
  }

  return expr::term_ref();
}

expr::term_ref solvers::eq_to_ineq(expr::term_ref G) {

  std::vector<expr::term_ref> G_new;

  // Get the conjuncts
  const expr::term& G_term = d_tm.term_of(G);
  if (G_term.op() != expr::TERM_AND) { return G; }
  for (size_t i = 0; i < G_term.size(); ++ i) {
    const expr::term& t = d_tm.term_of(G_term[i]);
    expr::term_ref lhs = t[0];
    expr::term_ref rhs = t[1];
    if (t.op() == expr::TERM_EQ && d_tm.is_subtype_of(d_tm.type_of(lhs), d_tm.real_type())) {
      G_new.push_back(d_tm.mk_term(expr::TERM_LEQ, lhs, rhs));
      G_new.push_back(d_tm.mk_term(expr::TERM_GEQ, lhs, rhs));
    } else {
      G_new.push_back(G_term[i]);
    }
  }

  return d_tm.mk_and(G_new);
}

expr::term_ref solvers::generalize_sat(smt::solver* solver) {
  std::vector<expr::term_ref> generalization_facts;
  solver->generalize(smt::solver::GENERALIZE_BACKWARD, generalization_facts);
  expr::term_ref G = d_tm.mk_and(generalization_facts);
  G = eq_to_ineq(G);
  return G;
}

expr::term_ref solvers::learn_forward(size_t k, expr::term_ref G) {

  TRACE("ic3") << "learning forward to refute: " << G << std::endl;

  assert(k > 0);

  // The solvers we'll be using
  smt::solver* I1_solver = 0;
  smt::solver* I2_solver = 0;

  if (d_ctx.get_options().get_bool("ic3-single-solver")) {
    I1_solver = get_reachability_solver();
    I2_solver = get_reachability_solver();
  } else {
    I1_solver = get_reachability_solver(k-1);
    I2_solver = get_reachability_solver(0);
  }

  // If we don't have interpolation, just learn not G
  if (!I1_solver->supports(smt::solver::INTERPOLATION)) {
    return d_tm.mk_term(expr::TERM_NOT, G);
  }

  // Get the interpolant I1 for: (R_{k-1} and T => I1, I1 and G unsat
  I1_solver->push();
  if (d_ctx.get_options().get_bool("ic3-single-solver")) {
    assert_frame_selection(k-1, I1_solver);
  }
  expr::term_ref G_next = d_transition_system->get_state_type()->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, G);
  I1_solver->add(G_next, smt::solver::CLASS_B);
  smt::solver::result I1_result = I1_solver->check();
  unused_var(I1_result);
  assert(I1_result == smt::solver::UNSAT);
  expr::term_ref I1 = I1_solver->interpolate();
  I1 = d_transition_system->get_state_type()->change_formula_vars(system::state_type::STATE_NEXT, system::state_type::STATE_CURRENT, I1);
  I1_solver->pop();

  TRACE("ic3") << "I1: " << I1 << std::endl;

  // Get the interpolant I2 for I => I2, I2 and G unsat
  I2_solver->push();
  if (d_ctx.get_options().get_bool("ic3-single-solver")) {
    assert_frame_selection(0, I2_solver);
  }
  I2_solver->add(G, smt::solver::CLASS_B);
  smt::solver::result I2_result = I2_solver->check();
  unused_var(I2_result);
  assert(I2_result == smt::solver::UNSAT);
  expr::term_ref I2 = I2_solver->interpolate();
  I2_solver->pop();

  TRACE("ic3") << "I2: " << I2 << std::endl;

  // Result is the disjunction of the two
  expr::term_ref learnt = d_tm.mk_term(expr::TERM_OR, I1, I2);

  return learnt;
}

expr::term_ref solvers::check_inductive(expr::term_ref f) {

  // Push the scoppe
  smt::solver* solver = get_induction_solver();
  smt::solver_scope scope(solver);
  scope.push();

  // Add the formula (moving current -> next)
  expr::term_ref F_not = d_tm.mk_term(expr::TERM_NOT, f);
  expr::term_ref F_not_next = d_transition_system->get_state_type()->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, F_not);
  solver->add(F_not_next, smt::solver::CLASS_B);

  // Figure out the result
  expr::term_ref result;
  smt::solver::result r = solver->check();
  switch (r) {
  case smt::solver::SAT: {
    result = generalize_sat(solver);
    break;
  }
  case smt::solver::UNSAT:
    // Unsat, we return NULL
    break;
  default:
    throw exception("SMT unknown result.");
  }

  return result;
}

expr::term_ref solvers::get_frame_variable(size_t k) {
  while (d_frame_variables.size() <= k) {
    std::stringstream ss;
    ss << "frame_" << k;
    expr::term_ref var = d_tm.mk_variable(ss.str(), d_tm.boolean_type());
    d_frame_variables.push_back(var);
  }
  return d_frame_variables[k];
}

void solvers::gc_collect(const expr::gc_relocator& gc_reloc) {
  gc_reloc.reloc(d_frame_variables);
}

void solvers::add(size_t k, expr::term_ref f)  {

  assert(k < d_size);

  // Add appropriately
  if (d_ctx.get_options().get_bool("ic3-single-solver")) {
    // Add te enabling variable and the implication to enable the assertion
    expr::term_ref assertion = d_tm.mk_term(expr::TERM_IMPLIES, get_frame_variable(k), f);
    get_reachability_solver()->add(assertion, smt::solver::CLASS_A);
  } else {
    // Add directly
    get_reachability_solver(k)->add(f, smt::solver::CLASS_A);
  }

  // If at induction frame, add to induction solver
  if (k + 1 == d_size) {
    get_induction_solver()->add(f, smt::solver::CLASS_A);
  }
}

void solvers::new_frame() {
  // Make sure we have counter-examples space for 0, ..., size
  ensure_counterexample_solver_depth(d_size);
  // Add the frame selection variable if needed
  if (d_ctx.get_options().get_bool("ic3-single-solver")) {
    expr::term_ref frame_var = get_frame_variable(d_size);
    get_reachability_solver()->add_variable(frame_var, smt::solver::CLASS_A);
  }
  // Increase the size
  d_size ++;
  // Reset the induction solver
  delete d_induction_solver;
  d_induction_solver = 0;
}

size_t solvers::size() {
  return d_size;
}

}
}
