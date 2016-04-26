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

#include "engine/ic3/solvers.h"

#include "smt/factory.h"
#include "utils/trace.h"

#include <iostream>
#include <fstream>

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
, d_initial_solver(0)
, d_induction_solver(0)
, d_induction_generalizer(0)
, d_minimization_solver(0)
, d_induction_solver_depth(0)
, d_counterexample_solver(0)
, d_counterexample_solver_depth(0)
, d_counterexample_solver_variables_depth(0)
, d_generate_models_for_queries(false)
{
}

solvers::~solvers() {
  delete d_reachability_solver;
  delete d_initial_solver;
  delete d_induction_solver;
  delete d_induction_generalizer;
  delete d_counterexample_solver;
  delete d_minimization_solver;
  for (size_t k = 0; k < d_reachability_solvers.size(); ++ k) {
    delete d_reachability_solvers[k];
  }
}

void solvers::reset(const std::vector<solvers::formula_set>& frames) {

  MSG(1) << "ic3: restarting solvers" << std::endl;

  if (d_ctx.get_options().get_bool("ic3-single-solver")) {
    // Restart the reachability solver
    delete d_reachability_solver;
    d_reachability_solver = 0;
  } else {
    // Restart the solver
    assert(d_size == d_reachability_solvers.size());
    assert(d_size == frames.size());
    for (size_t k = 0; k < d_size; ++ k) {
      delete d_reachability_solvers[k];
      d_reachability_solvers[k] = 0;
    }
    d_reachability_solvers.clear();
  }

  // Clear the initial solver
  delete d_initial_solver;
  d_initial_solver = 0;

  // Clear the induction solver
  delete d_induction_solver;
  d_induction_solver = 0;
  delete d_induction_generalizer;
  d_induction_generalizer = 0;

  // Reset the counterexample solver
  delete d_counterexample_solver;
  d_counterexample_solver = 0;
  d_counterexample_solver_depth = 0;
  d_counterexample_solver_variables_depth = 0;

  // Reset the minimization solver
  delete d_minimization_solver;
  d_minimization_solver = 0;

  assert(d_size == frames.size());
  ensure_counterexample_solver_depth(d_size-1);

  // Add the frame content
  for (size_t k = 0; k < frames.size(); ++ k) {
    // Add the content again
    formula_set::const_iterator it = frames[k].begin();
    for (; it != frames[k].end(); ++ it) {
      add_to_reachability_solver(k, *it);
    }
  }
}

void solvers::init_reachability_solver(size_t k) {

  assert(!d_ctx.get_options().get_bool("ic3-single-solver"));
  assert(k < d_size);

  if (d_reachability_solvers.size() <= k) {

    // The variables from the state types
    const std::vector<expr::term_ref>& x = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_CURRENT);
    const std::vector<expr::term_ref>& x_next = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_NEXT);
    const std::vector<expr::term_ref>& input = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_INPUT);

    // A solver per frame
    while (d_reachability_solvers.size() <= k) {
      smt::solver* solver = smt::factory::mk_default_solver(d_tm, d_ctx.get_options(), d_ctx.get_statistics());
      d_reachability_solvers.push_back(solver);
      solver->add_variables(x.begin(), x.end(), smt::solver::CLASS_A);
      solver->add_variables(x_next.begin(), x_next.end(), smt::solver::CLASS_B);
      solver->add_variables(input.begin(), input.end(), smt::solver::CLASS_T);
      // Add transition relation
      solver->add(d_transition_system->get_transition_relation(), smt::solver::CLASS_T);
      if (d_reachability_solvers.size() == 1) {
        solver->add(d_transition_system->get_initial_states(), smt::solver::CLASS_A);
      }
    }
  }
}

void solvers::ensure_counterexample_solver_depth(size_t k) {
  // Make sure we unrolled the solver variables up to k
  for (; d_counterexample_solver_variables_depth <= k; ++ d_counterexample_solver_variables_depth) {
    // Add state variables
    const std::vector<expr::term_ref>& state_variables = d_trace->get_state_variables(d_counterexample_solver_variables_depth);
    get_counterexample_solver()->add_variables(state_variables.begin(), state_variables.end(), smt::solver::CLASS_A);
    // Add input variables to get here
    if (d_counterexample_solver_variables_depth > 0) {
      const std::vector<expr::term_ref>& input_variables = d_trace->get_input_variables(d_counterexample_solver_variables_depth-1);
      get_counterexample_solver()->add_variables(input_variables.begin(), input_variables.end(), smt::solver::CLASS_A);
    }
  }
  // Make sure we unrolled the solver up to k
  for (; d_counterexample_solver_depth < k; ++ d_counterexample_solver_depth) {
    // Add transition relation k -> k + 1 to the counter-example solver
    expr::term_ref T = d_trace->get_transition_formula(d_transition_system->get_transition_relation(), d_counterexample_solver_depth);
    get_counterexample_solver()->add(T, smt::solver::CLASS_A);
  }
}

smt::solver* solvers::get_initial_solver() {
  if (d_initial_solver == 0) {
    // The variables from the state types
    const std::vector<expr::term_ref>& x = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_CURRENT);
    // Make the solver
    d_initial_solver = smt::factory::mk_default_solver(d_tm, d_ctx.get_options(), d_ctx.get_statistics());
    d_initial_solver->add_variables(x.begin(), x.end(), smt::solver::CLASS_A);
    d_initial_solver->add(d_transition_system->get_initial_states(), smt::solver::CLASS_A);
  }
  return d_initial_solver;
}


smt::solver* solvers::get_reachability_solver() {
  assert(d_ctx.get_options().get_bool("ic3-single-solver"));
  if (d_reachability_solver == 0) {
    // The variables from the state types
    const std::vector<expr::term_ref>& x = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_CURRENT);
    const std::vector<expr::term_ref>& x_next = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_NEXT);
    const std::vector<expr::term_ref>& input = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_INPUT);
    // Make the solver
    d_reachability_solver = smt::factory::mk_default_solver(d_tm, d_ctx.get_options(), d_ctx.get_statistics());
    d_reachability_solver->add_variables(x.begin(), x.end(), smt::solver::CLASS_A);
    d_reachability_solver->add_variables(x_next.begin(), x_next.end(), smt::solver::CLASS_B);
    d_reachability_solver->add_variables(input.begin(), input.end(), smt::solver::CLASS_T);
    d_reachability_solver->add(d_transition_system->get_transition_relation(), smt::solver::CLASS_T);
  }
  return d_reachability_solver;
}

smt::solver* solvers::get_reachability_solver(size_t k) {
  assert(!d_ctx.get_options().get_bool("ic3-single-solver"));
  init_reachability_solver(k);
  return d_reachability_solvers[k];
}

smt::solver* solvers::get_minimization_solver() {
  if (d_minimization_solver == 0) {
    // Make the solver
    const std::vector<expr::term_ref>& x = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_CURRENT);
    d_minimization_solver = smt::factory::mk_default_solver(d_tm, d_ctx.get_options(), d_ctx.get_statistics());
    d_minimization_solver->add_variables(x.begin(), x.end(), smt::solver::CLASS_A);
  }
  return d_minimization_solver;
}


smt::solver* solvers::get_counterexample_solver() {
  if (d_counterexample_solver == 0) {
    // Make the solver
    d_counterexample_solver = smt::factory::mk_default_solver(d_tm, d_ctx.get_options(), d_ctx.get_statistics());
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
  if (d_initial_solver) {
    d_initial_solver->gc();
  }
  if (d_induction_solver) {
    d_induction_solver->gc();
  }
  if (d_induction_generalizer) {
    d_induction_generalizer->gc();
  }
  if (d_reachability_solver) {
    d_reachability_solver->gc();
  }
}

void solvers::assert_frame_selection(size_t k, smt::solver* solver) {
  bool multiple = true;

  if (multiple) {
    // Add the frame
    expr::term_ref frame_variable = get_frame_variable(k);
    solver->add(frame_variable, smt::solver::CLASS_A);
    // Add the rest
    for (size_t i = 0; i < d_size; ++ i) {
      frame_variable = get_frame_variable(i);
      if (i != k) {
        solver->add(d_tm.mk_term(expr::TERM_NOT, frame_variable), smt::solver::CLASS_A);
      }
    }
  } else {
    expr::term_ref frame_variable = get_frame_variable(k);
    solver->add(frame_variable, smt::solver::CLASS_A);
  }
}

solvers::query_result::query_result()
: result(smt::solver::UNKNOWN)
, model(0)
{
}

smt::solver::result solvers::query_at_init(expr::term_ref f) {
  smt::solver* solver = get_initial_solver();
  smt::solver_scope scope(solver);
  scope.push();

  query_result result;

  solver->add(f, smt::solver::CLASS_A);
  return solver->check();
}

solvers::query_result solvers::query_with_transition_at(size_t k, expr::term_ref f, smt::solver::formula_class f_class) {

  smt::solver* solver = 0;
  query_result result;

  if (d_ctx.get_options().get_bool("ic3-single-solver")) {
    solver = get_reachability_solver();
  } else {
    solver = get_reachability_solver(k);
  }
  smt::solver_scope scope(solver);

  // Add the formula
  scope.push();
  solver->add(f, f_class);

  // Add frame selection if needed
  if (d_ctx.get_options().get_bool("ic3-single-solver")) {
    assert_frame_selection(k, solver);
  }

  // Figure out the result
  result.result = solver->check();
  switch (result.result) {
  case smt::solver::SAT: {
    if (d_generate_models_for_queries) {
      result.model = solver->get_model();
    }
    result.generalization = generalize_sat(solver);
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

expr::term_ref solvers::eq_to_ineq(expr::term_ref G) {

  std::vector<expr::term_ref> G_new;

  const expr::term& G_term = d_tm.term_of(G);

  // If pure equality just split it
  if (G_term.op() == expr::TERM_EQ) {
    expr::term_ref lhs = G_term[0];
    expr::term_ref rhs = G_term[1];
    if (d_tm.is_subtype_of(d_tm.type_of(lhs), d_tm.real_type())) {
      G_new.push_back(d_tm.mk_term(expr::TERM_LEQ, lhs, rhs));
      G_new.push_back(d_tm.mk_term(expr::TERM_GEQ, lhs, rhs));
      return d_tm.mk_and(G_new);
    } else {
      return G;
    }
  }

  // If conjunction, split the conjuncts
  if (G_term.op() == expr::TERM_AND) {
    for (size_t i = 0; i < G_term.size(); ++ i) {
      const expr::term& t = d_tm.term_of(G_term[i]);
      if (t.op() == expr::TERM_EQ) {
        expr::term_ref lhs = t[0];
        expr::term_ref rhs = t[1];
        if (d_tm.is_subtype_of(d_tm.type_of(lhs), d_tm.real_type())) {
          G_new.push_back(d_tm.mk_term(expr::TERM_LEQ, lhs, rhs));
          G_new.push_back(d_tm.mk_term(expr::TERM_GEQ, lhs, rhs));
        } else {
          G_new.push_back(G_term[i]);
        }
      } else {
        G_new.push_back(G_term[i]);
      }
    }
    return d_tm.mk_and(G_new);
  }

  return G;
}

expr::term_ref solvers::generalize_sat(smt::solver* solver) {
  // Generalize
  std::vector<expr::term_ref> generalization_facts;
  solver->generalize(smt::solver::GENERALIZE_BACKWARD, generalization_facts);
  if (d_ctx.get_options().get_bool("ic3-minimize-generalizations")) {
    // Add negation of generalization
    smt::solver* minimization_solver = get_minimization_solver();
    smt::solver_scope scope(minimization_solver);
    scope.push();
    minimization_solver->add(d_tm.mk_not(d_tm.mk_and(generalization_facts)), smt::solver::CLASS_A);
    // Get all the conjuncts
    std::set<expr::term_ref> conjuncts;
    for (size_t i = 0; i < generalization_facts.size(); ++ i) {
      d_tm.get_conjuncts(generalization_facts[i], conjuncts);
    }
    std::vector<expr::term_ref> conjuncts_vec(conjuncts.begin(), conjuncts.end()), minimized_vec;
    // Minimize
    quickxplain_generalization(minimization_solver, conjuncts_vec, 0, conjuncts_vec.size(), minimized_vec);
    TRACE("ic3::mingen") << "min: old_size = " << conjuncts_vec.size() << ", new_size = " << minimized_vec.size() << std::endl;
    generalization_facts.swap(minimized_vec);
  }
  expr::term_ref G = d_tm.mk_and(generalization_facts);
  // Move variables back to regular state instead of trace state
  G = d_trace->get_state_formula(0, G);
  return G;
}

expr::term_ref solvers::generalize_sat(smt::solver* solver, expr::model::ref m) {
  // Generalize
  std::vector<expr::term_ref> generalization_facts;
  solver->generalize(smt::solver::GENERALIZE_BACKWARD, m, generalization_facts);
  if (d_ctx.get_options().get_bool("ic3-minimize-generalizations")) {
    // Add negation of generalization
    smt::solver* minimization_solver = get_minimization_solver();
    smt::solver_scope scope(minimization_solver);
    scope.push();
    minimization_solver->add(d_tm.mk_not(d_tm.mk_and(generalization_facts)), smt::solver::CLASS_A);
    // Get all the conjuncts
    std::set<expr::term_ref> conjuncts;
    for (size_t i = 0; i < generalization_facts.size(); ++ i) {
      d_tm.get_conjuncts(generalization_facts[i], conjuncts);
    }
    // Minimize
    std::vector<expr::term_ref> conjuncts_vec(conjuncts.begin(), conjuncts.end()), minimized_vec;
    quickxplain_generalization(minimization_solver, conjuncts_vec, 0, conjuncts_vec.size(), minimized_vec);
    TRACE("ic3::mingen") << "min: old_size = " << conjuncts_vec.size() << ", new_size = " << minimized_vec.size() << std::endl;
    generalization_facts.swap(minimized_vec);
  }
  expr::term_ref G = d_tm.mk_and(generalization_facts);
  // Move variables back to regular state instead of trace state
  G = d_trace->get_state_formula(0, G);
  return G;
}

void solvers::quickxplain_interpolant(smt::solver* I_solver, smt::solver* T_solver, const std::vector<expr::term_ref>& disjuncts, size_t begin, size_t end, std::vector<expr::term_ref>& out) {

  // TRACE("ic3::min") << "min: begin = " << begin << ", end = " << end << std::endl;

  smt::solver_scope I_solver_scope(I_solver);
  smt::solver_scope T_solver_scope(T_solver);

  smt::solver::result I_solver_result = smt::solver::UNSAT;
  smt::solver::result T_solver_result = smt::solver::UNSAT;

  if (I_solver) { I_solver_result = I_solver->check(); }
  if (T_solver) { T_solver_result = T_solver->check(); }

  if (I_solver_result == smt::solver::UNSAT && T_solver_result == smt::solver::UNSAT) {
    // Solver state already unsat, done
    return;
  }

  // If only one solver is unsat, we don't use it anymore
  if (I_solver_result == smt::solver::UNSAT) { I_solver = 0; }
  if (T_solver_result == smt::solver::UNSAT) { T_solver = 0; }

  assert(begin < end);

  if (begin + 1 == end) {
    // Only one left, we keep it, since we're SAT in one of the solvers
    out.push_back(disjuncts[begin]);
    return;
  }

  // Split: how many in first half?
  size_t n = (end - begin) / 2;

  // Assert first half and minimize the second
  if (I_solver) I_solver_scope.push();
  if (T_solver) T_solver_scope.push();
  for (size_t i = begin; i < begin + n; ++ i) {
    expr::term_ref to_assert = d_tm.mk_term(expr::TERM_NOT, disjuncts[i]);
    // Add to initial solver
    if (I_solver) {
      I_solver->add(to_assert, smt::solver::CLASS_A);
    }
    // Add to transition solver
    if (T_solver) {
      to_assert = d_transition_system->get_state_type()->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, to_assert);
      T_solver->add(to_assert, smt::solver::CLASS_A);
    }
  }
  size_t old_out_size = out.size();
  quickxplain_interpolant(I_solver, T_solver, disjuncts, begin + n, end, out);
  if (I_solver) I_solver_scope.pop();
  if (T_solver) T_solver_scope.pop();

  // Now, assert the minimized second half, and minimize the first half
  if (I_solver) I_solver_scope.push();
  if (T_solver) T_solver_scope.push();
  for (size_t i = old_out_size; i < out.size(); ++ i) {
    expr::term_ref to_assert = d_tm.mk_term(expr::TERM_NOT, out[i]);
    // Add to initial solver
    if (I_solver) {
      I_solver->add(to_assert, smt::solver::CLASS_A);
    }
    // Add to transition solver
    if (T_solver) {
      to_assert = d_transition_system->get_state_type()->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, to_assert);
      T_solver->add(to_assert, smt::solver::CLASS_A);
    }
  }
  quickxplain_interpolant(I_solver, T_solver, disjuncts, begin, begin + n, out);
  if (I_solver) I_solver_scope.pop();
  if (T_solver) T_solver_scope.pop();
}

void solvers::quickxplain_generalization(smt::solver* solver, const std::vector<expr::term_ref>& conjuncts, size_t begin, size_t end, std::vector<expr::term_ref>& out) {

  // TRACE("ic3::min") << "min: begin = " << begin << ", end = " << end << std::endl;

  smt::solver_scope solver_scope(solver);
  smt::solver::result solver_result = solver->check();

  if (solver_result == smt::solver::UNSAT) {
    // Solver state already unsat, done
    return;
  }

  assert(begin < end);

  if (begin + 1 == end) {
    // Only one left, we keep it, since we're SAT in one of the solvers
    out.push_back(conjuncts[begin]);
    return;
  }

  // Split: how many in first half?
  size_t n = (end - begin) / 2;

  // Assert first half and minimize the second
  solver_scope.push();
  for (size_t i = begin; i < begin + n; ++ i) {
    solver->add(conjuncts[i], smt::solver::CLASS_A);
  }
  size_t old_out_size = out.size();
  quickxplain_generalization(solver, conjuncts, begin + n, end, out);
  solver_scope.pop();

  // Now, assert the minimized second half, and minimize the first half
  solver_scope.push();
  for (size_t i = old_out_size; i < out.size(); ++ i) {
    solver->add(out[i], smt::solver::CLASS_A);
  }
  quickxplain_generalization(solver, conjuncts, begin, begin + n, out);
  solver_scope.pop();
}


expr::term_ref solvers::learn_forward(size_t k, expr::term_ref G) {

  TRACE("ic3") << "learning forward to refute: " << G << std::endl;

  // Get the interpolant I2 for I => I2, I2 and G unsat
  smt::solver* I_solver = get_initial_solver();
  if (!I_solver->supports(smt::solver::INTERPOLATION)) {
    return d_tm.mk_term(expr::TERM_NOT, G);
  }

  I_solver->push();
  I_solver->add(G, smt::solver::CLASS_B);
  smt::solver::result I_result = I_solver->check();
  unused_var(I_result);
  assert(I_result == smt::solver::UNSAT);
  expr::term_ref I_I = I_solver->interpolate();
  I_solver->pop();

  TRACE("ic3") << "I_I: " << I_I << std::endl;

  if (k == 0) {
    // If refuting at 0, it's just I
    return I_I;
  }

  // Transition solver
  smt::solver* T_solver = 0;
  if (d_ctx.get_options().get_bool("ic3-single-solver")) {
    T_solver = get_reachability_solver();
  } else {
    T_solver = get_reachability_solver(k-1);
  }

  // Get the interpolant T_I for: (R_{k-1} and T => T_I, T_I and G unsat
  T_solver->push();
  if (d_ctx.get_options().get_bool("ic3-single-solver")) {
    assert_frame_selection(k-1, T_solver);
  }
  expr::term_ref G_next = d_transition_system->get_state_type()->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, G);
  T_solver->add(G_next, smt::solver::CLASS_B);
  smt::solver::result T_result = T_solver->check();
  unused_var(T_result);
  assert(T_result == smt::solver::UNSAT);
  expr::term_ref T_I = T_solver->interpolate();
  T_I = d_transition_system->get_state_type()->change_formula_vars(system::state_type::STATE_NEXT, system::state_type::STATE_CURRENT, T_I);
  T_solver->pop();

  TRACE("ic3") << "T_I: " << T_I << std::endl;

  expr::term_ref learnt;

  if (d_ctx.get_options().get_bool("ic3-minimize-interpolants")) {
    // Get all the disjuncts
    std::set<expr::term_ref> disjuncts;
    d_tm.get_disjuncts(I_I, disjuncts);
    d_tm.get_disjuncts(T_I, disjuncts);
    std::vector<expr::term_ref> disjuncts_vec(disjuncts.begin(), disjuncts.end()), minimized_vec;
    quickxplain_interpolant(I_solver, T_solver, disjuncts_vec, 0, disjuncts_vec.size(), minimized_vec);
    TRACE("ic3::min") << "min: old_size = " << disjuncts_vec.size() << ", new_size = " << minimized_vec.size() << std::endl;
    learnt = d_tm.mk_or(minimized_vec);
  } else {
    // Result is the disjunction of the two
    learnt = d_tm.mk_or(T_I, I_I);
  }

  TRACE("ic3") << "leaned: " << learnt << std::endl;

  return learnt;
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

void solvers::add_to_reachability_solver(size_t k, expr::term_ref f)  {

  assert(k > 0);
  assert(k < d_size);

  // Add appropriately
  if (d_ctx.get_options().get_bool("ic3-single-solver")) {
    // Add te enabling variable and the implication to enable the assertion
    expr::term_ref assertion = d_tm.mk_term(expr::TERM_IMPLIES, get_frame_variable(k), f);
    smt::solver* solver = get_reachability_solver();
    solver->add(assertion, smt::solver::CLASS_A);
  } else {
    // Add directly
    smt::solver* solver = get_reachability_solver(k);
    solver->add(f, smt::solver::CLASS_A);
    if (d_ctx.get_options().get_bool("ic3-check-deadlock")) {
      smt::solver::result result = solver->check();
      if (result != smt::solver::SAT) {
        std::stringstream ss;
        ss << "ic3: deadlock detected at reachability frame " << k << ".";
        throw exception(ss.str());
      }
    }
  }
}

void solvers::reset_induction_solver(size_t depth) {
  // Reset the induction solver
  delete d_induction_solver;
  delete d_induction_generalizer;

  // Transition relation
  d_transition_relation = d_transition_system->get_transition_relation();

  // The solver
  d_induction_solver = smt::factory::mk_default_solver(d_tm, d_ctx.get_options(), d_ctx.get_statistics());
  d_induction_generalizer = smt::factory::mk_default_solver(d_tm, d_ctx.get_options(), d_ctx.get_statistics());
  d_induction_solver_depth = depth;

  // Add variables and transition relation
  for (size_t k = 0; k <= depth; ++ k) {

    // The variables
    const std::vector<expr::term_ref>& x = d_trace->get_state_variables(k);

    // Add state variables
    if (k == 0) {
      // First frame is A
      const std::vector<expr::term_ref>& x_state = d_transition_system->get_state_type()->get_variables(system::state_type::STATE_CURRENT);
      d_induction_solver->add_variables(x_state.begin(), x_state.end(), smt::solver::CLASS_A);
      d_induction_generalizer->add_variables(x_state.begin(), x_state.end(), smt::solver::CLASS_A);
    } else if (k < depth) {
      // Intermediate frames are T
      d_induction_solver->add_variables(x.begin(), x.end(), smt::solver::CLASS_T);
      d_induction_generalizer->add_variables(x.begin(), x.end(), smt::solver::CLASS_T);
    } else {
      // Last frame is B
      d_induction_solver->add_variables(x.begin(), x.end(), smt::solver::CLASS_B);
      d_induction_generalizer->add_variables(x.begin(), x.end(), smt::solver::CLASS_B);
    }

    // Add input variables
    if (k > 0) {
      const std::vector<expr::term_ref>& input = d_trace->get_input_variables(k-1);
      d_induction_solver->add_variables(input.begin(), input.end(), smt::solver::CLASS_T);
      d_induction_generalizer->add_variables(input.begin(), input.end(), smt::solver::CLASS_T);
      // Formula T(x_{k-1}, x_k)
      expr::term_ref T = d_trace->get_transition_formula(d_transition_relation, k-1);
      // If transitioning from initial state, move to state vars
      if (k == 1) {
        T = d_trace->get_state_formula(0, T);
      }
      d_induction_solver->add(T, smt::solver::CLASS_T);
      d_induction_generalizer->add(T, smt::solver::CLASS_T);
    }
  }
}

void solvers::add_to_induction_solver(expr::term_ref f, induction_assertion_type type) {
  assert(d_induction_solver != 0);
  assert(d_induction_generalizer != 0);
  switch (type) {
  case INDUCTION_FIRST:
    d_induction_solver->add(f, smt::solver::CLASS_A);
    break;
  case INDUCTION_INTERMEDIATE:
    for (size_t k = 1; k < d_induction_solver_depth; ++ k) {
      d_induction_solver->add(d_trace->get_state_formula(f, k), smt::solver::CLASS_T);
    }
    break;
  default:
    assert(false);
  }

  if (d_ctx.get_options().get_bool("ic3-check-deadlock")) {
    smt::solver::result result = d_induction_solver->check();
    if (result != smt::solver::SAT) {
      std::stringstream ss;
      ss << "ic3: deadlock detected when checking induction of depth " << d_induction_solver_depth << ".";
      throw exception(ss.str());
    }
  }
}

solvers::query_result solvers::check_inductive(expr::term_ref f) {

  assert(d_induction_solver != 0);
  assert(d_induction_generalizer != 0);

  query_result result;

  // Push the scope
  smt::solver_scope scope(d_induction_solver);
  scope.push();

  // Add the formula (moving current -> next)
  expr::term_ref F_not = d_tm.mk_term(expr::TERM_NOT, f);
  expr::term_ref F_not_next = d_trace->get_state_formula(F_not, d_induction_solver_depth);
  d_induction_solver->add(F_not_next, smt::solver::CLASS_B);

  // Figure out the result
  result.result = d_induction_solver->check();
  switch (result.result) {
  case smt::solver::SAT: {
    // Generalize in the simplified induction
    result.model = d_induction_solver->get_model();
    smt::solver_scope scope(d_induction_generalizer);
    scope.push();
    d_induction_generalizer->add(F_not_next, smt::solver::CLASS_B);
    result.generalization = generalize_sat(d_induction_generalizer, result.model);
    break;
  }
  case smt::solver::UNSAT:
    break;
  default:
    throw exception("SMT unknown result.");
  }

  return result;
}

solvers::query_result solvers::check_inductive_model(expr::model::ref m, expr::term_ref f) {
  assert(d_induction_solver != 0);
  assert(d_induction_generalizer != 0);

  solvers::query_result result;

  expr::term_ref f_next = d_trace->get_state_formula(f, d_induction_solver_depth);
  if (m->is_true(f_next)) {
    result.model = m;
    result.result = smt::solver::SAT;

    smt::solver_scope scope(d_induction_generalizer);
    scope.push();
    d_induction_generalizer->add(f_next, smt::solver::CLASS_B);
    result.generalization = generalize_sat(d_induction_generalizer, m);
  } else {
    result.result = smt::solver::UNSAT;
  }

  return result;
}

void solvers::new_reachability_frame() {
  // Make sure we have counter-examples space for 0, ..., size
  ensure_counterexample_solver_depth(d_size);
  // Add the frame selection variable if needed
  if (d_ctx.get_options().get_bool("ic3-single-solver")) {
    expr::term_ref frame_var = get_frame_variable(d_size);
    get_reachability_solver()->add_variable(frame_var, smt::solver::CLASS_A);
  }
  // Increase the size
  d_size ++;
}

size_t solvers::size() {
  return d_size;
}

void solvers::generate_models_for_queries(bool flag) {
  d_generate_models_for_queries = flag;
}

void solvers::output_efsmt(expr::term_ref f, expr::term_ref g) const {

  assert(false); // TODO: not current with the changes to induction solver
  assert(!f.is_null());
  assert(!g.is_null());

  static size_t i = 0;

  // we have
  //  \forall x G(x) => \exists x' T(x, x') and f is valid
  //  G(x) and \forall y not (T(x, x') and f') is unsat

  std::stringstream ss;
  ss << "ic3_gen_check_" << i++ << ".smt2";
  std::ofstream out(ss.str().c_str());

  out << expr::set_tm(d_tm);

  out << "(set-logic LRA)" << std::endl;
  out << "(set-info :smt-lib-version 2.0)" << std::endl;
  out << "(set-info :status unsat)" << std::endl;
  out << std::endl;

  const system::state_type* state_type = d_transition_system->get_state_type();

  const std::vector<expr::term_ref>& state_vars = state_type->get_variables(system::state_type::STATE_CURRENT);
  const std::vector<expr::term_ref>& input_vars = state_type->get_variables(system::state_type::STATE_INPUT);
  const std::vector<expr::term_ref>& next_vars = state_type->get_variables(system::state_type::STATE_NEXT);

  for (size_t i = 0; i < state_vars.size(); ++ i) {
    expr::term_ref variable = state_vars[i];
    out << "(declare-fun " << variable << " () " << d_tm.type_of(variable) << ")" << std::endl;
  }

  out << std::endl;
  out << ";; generalization" << std::endl;
  out << "(assert " << g << ")" << std::endl;

  out << std::endl;
  out << "(assert (forall (";
  for (size_t i = 0; i < input_vars.size(); ++ i) {
    expr::term_ref variable = input_vars[i];
    if (i) out << " ";
    out << "(";
    out << variable << " " << d_tm.type_of(variable);
    out << ")";
  }
  for (size_t i = 0; i < next_vars.size(); ++ i) {
    expr::term_ref variable = next_vars[i];
    out << " (";
    out << variable << " " << d_tm.type_of(variable);
    out << ")";
  }
  out << ")" << std::endl; // end forall variables
  out << "(not (and" << std::endl;
  out << "  " << d_transition_system->get_transition_relation() << std::endl;
  out << "  " << state_type->change_formula_vars(system::state_type::STATE_CURRENT, system::state_type::STATE_NEXT, f) << std::endl;
  out << "))" << std::endl; // end negation and and

  out << "))" << std::endl; // end forall

  out << std::endl;
  out << "(check-sat)" << std::endl;
}

void solvers::quickxplain_frame(smt::solver* solver, const std::vector<induction_obligation>& frame, size_t begin, size_t end, std::vector<induction_obligation>& out) {
  smt::solver_scope solver_scope(solver);

  assert(begin < end);

  if (begin == end) {
    return;
  }

  if (begin + 1 == end) {
    // Keep the properties
    if (frame[begin].d == 0) {
      out.push_back(frame[begin]);
      return;
    }
    // Only one left, we keep it, check if we need it
    solver_scope.push();
    expr::term_ref f_not = d_tm.mk_not(frame[begin].F_fwd);
    solver->add(f_not, smt::solver::CLASS_A);
    if (solver->check() != smt::solver::UNSAT) {
      out.push_back(frame[begin]);
    }
    return;
  }

  // Split: how many in first half?
  size_t n = (end - begin) / 2;

  // Assert first half and minimize the second
  solver_scope.push();
  for (size_t i = begin; i < begin + n; ++ i) {
    solver->add(frame[i].F_fwd, smt::solver::CLASS_A);
  }
  size_t old_out_size = out.size();
  quickxplain_frame(solver, frame, begin + n, end, out);
  solver_scope.pop();

  // Now, assert the minimized second half, and minimize the first half
  solver_scope.push();
  for (size_t i = old_out_size; i < out.size(); ++ i) {
    solver->add(out[i].F_fwd, smt::solver::CLASS_A);
  }
  quickxplain_frame(solver, frame, begin, begin + n, out);
  solver_scope.pop();

}

void solvers::minimize_frame(std::vector<induction_obligation>& frame) {
  std::vector<induction_obligation> out;
  smt::solver* solver = get_minimization_solver();
  quickxplain_frame(solver, frame, 0, frame.size(), out);
  frame.swap(out);
}

}
}
