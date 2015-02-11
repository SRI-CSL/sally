/*
 * incremental_wrapper.cpp
 *
 *  Created on: Feb 8, 2015
 *      Author: dejan
 */

#include "smt/incremental_wrapper.h"

namespace sally {
namespace smt {

incremental_wrapper::incremental_wrapper(std::string name, expr::term_manager& tm, const options& opts, solver_constructor* constructor)
: solver(name, tm, opts)
, d_constructor(constructor)
{
  d_solver = d_constructor->mk_solver();
}

incremental_wrapper::~incremental_wrapper() {
  delete d_solver;
  delete d_constructor;
}

bool incremental_wrapper::supports(feature f) const {
  return d_solver->supports(f);
}

void incremental_wrapper::add(expr::term_ref f, formula_class f_class) {
  d_assertions.push_back(assertion(f, f_class));
}

solver::result incremental_wrapper::check() {

  delete d_solver;
  d_solver = d_constructor->mk_solver();

  // Initialize solver
  d_solver->add_x_variables(d_x_variables.begin(), d_x_variables.end());
  d_solver->add_y_variables(d_y_variables.begin(), d_y_variables.end());

  // Assert the formulas
  for (size_t i = 0; i < d_assertions.size(); ++ i) {
    d_solver->add(d_assertions[i].f, d_assertions[i].f_class);
  }

  // Check and interpolate
  return d_solver->check();
}

void incremental_wrapper::get_model(expr::model& m) const {
  d_solver->get_model(m);
}

void incremental_wrapper::push() {
  d_assertions_size.push_back(d_assertions.size());
}

void incremental_wrapper::pop() {
  size_t size = d_assertions_size.back();
  d_assertions_size.pop_back();
  while (d_assertions.size() > size) {
    d_assertions.pop_back();
  }
}

void incremental_wrapper::generalize(std::vector<expr::term_ref>& out) {
  d_solver->generalize(out);
}

void incremental_wrapper::interpolate(std::vector<expr::term_ref>& out) {
  d_solver->interpolate(out);
}

void incremental_wrapper::get_unsat_core(std::vector<expr::term_ref>& out) {
  d_solver->get_unsat_core(out);
}

}
}

