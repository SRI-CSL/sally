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

expr::term_ref solver::generalize(generalization_type type) {
  std::vector<expr::term_ref> projection_out;
  generalize(type, projection_out);
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
  case solver::CLASS_T: out << "CLASS_T"; break;
  case solver::CLASS_B: out << "CLASS B"; break;
  default:
    assert(false);
  }
  return out;
}

}
}
