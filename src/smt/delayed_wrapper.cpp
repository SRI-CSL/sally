/*
 * delayed_wrapper.cpp
 *
 *  Created on: Feb 8, 2015
 *      Author: dejan
 */

#include "smt/delayed_wrapper.h"

namespace sally {
namespace smt {

delayed_wrapper::delayed_wrapper(std::string name, expr::term_manager& tm, const options& opts, solver* s)
: solver(name, tm, opts)
, d_solver(s)
, d_index(0)
, d_scope(0)
{
}

delayed_wrapper::~delayed_wrapper() {
  delete d_solver;
}

bool delayed_wrapper::supports(feature f) const {
  return d_solver->supports(f);
}

void delayed_wrapper::add(expr::term_ref f, formula_class f_class) {
  d_assertions.push_back(assertion(f, f_class));
}

solver::result delayed_wrapper::check() {

  for (; d_index < d_assertions.size(); ++ d_index) {
    if (d_scope < d_assertions_size.size() && d_index == d_assertions_size[d_scope]) {
      d_scope ++;
      d_solver->push();
    }
    d_solver->add(d_assertions[d_index].f, d_assertions[d_index].f_class);
  }

  return d_solver->check();
}

void delayed_wrapper::get_model(expr::model& m) const {
  d_solver->get_model(m);
}

void delayed_wrapper::push() {
  d_assertions_size.push_back(d_assertions.size());
}

void delayed_wrapper::pop() {
  // Pop the assertions stack
  size_t size = d_assertions_size.back();
  d_assertions_size.pop_back();
  while (d_assertions.size() > size) {
    d_assertions.pop_back();
  }
  // If we went below next one to process, also update
  if (d_assertions.size() < d_index) {
    d_index = d_assertions.size();
  }
  // If scope went below currently processed, also update
  if (d_assertions_size.size() < d_scope) {
    d_scope = d_assertions_size.size();
    d_solver->pop();
  }
}

void delayed_wrapper::generalize(std::vector<expr::term_ref>& out) {
  d_solver->generalize(out);
}

void delayed_wrapper::interpolate(std::vector<expr::term_ref>& out) {
  d_solver->interpolate(out);
}

void delayed_wrapper::add_x_variable(expr::term_ref x_var) {
  d_solver->add_x_variable(x_var);
}

void delayed_wrapper::add_y_variable(expr::term_ref y_var) {
  d_solver->add_y_variable(y_var);
}


}
}

