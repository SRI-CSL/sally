/*
 * solver.cpp
 *
 *  Created on: Oct 24, 2014
 *      Author: dejan
 */

#include "smt/solver.h"

#include <cassert>
#include <iostream>

namespace sally {
namespace smt {

std::ostream& operator << (std::ostream& out, solver::result result) {
  switch (result) {
  case solver::SAT:
    out << "sat";
    break;
  case solver::UNSAT:
    out << "unsat";
    break;
  case solver::UNKNOWN:
    out << "unknown";
    break;
  }
  return out;
}

expr::term_ref solver::generalize() {
  std::vector<expr::term_ref> projection_out;
  generalize(projection_out);
  return d_tm.mk_and(projection_out);
}

expr::term_ref solver::interpolate() {
  std::vector<expr::term_ref> interpolation_out;
  interpolate(interpolation_out);
  return d_tm.mk_and(interpolation_out);
}

void solver::add_x_variable(expr::term_ref x_var) {
  assert(d_x_variables.find(x_var) == d_x_variables.end());
  assert(d_y_variables.find(x_var) == d_y_variables.end());
  d_x_variables.insert(x_var);
}

void solver::add_y_variable(expr::term_ref y_var) {
  assert(d_x_variables.find(y_var) == d_x_variables.end());
  assert(d_y_variables.find(y_var) == d_y_variables.end());
  d_y_variables.insert(y_var);
}

std::ostream& operator << (std::ostream& out, solver::formula_class fc) {
  switch(fc) {
  case solver::CLASS_A: out << "CLASS A"; break;
  case solver::CLASS_B: out << "CLASS B"; break;
  default:
    assert(false);
  }
  return out;
}

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

}
}
