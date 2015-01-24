/*
 * solver.cpp
 *
 *  Created on: Oct 24, 2014
 *      Author: dejan
 */

#include "smt/solver.h"

#include <cassert>
#include <iostream>

namespace sal2 {
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
  generalize(interpolation_out);
  return d_tm.mk_and(interpolation_out);
}

void solver::add_x_variable(expr::term_ref x_var) {
  assert(d_x_variables.find(x_var) == d_x_variables.end());
  assert(d_y_variables.find(x_var) == d_y_variables.end());
  d_x_variables.insert(x_var);
}

void solver::add_y_variable(expr::term_ref x_var) {
  assert(d_x_variables.find(x_var) == d_x_variables.end());
  assert(d_y_variables.find(x_var) == d_y_variables.end());
  d_y_variables.insert(x_var);
}

}
}
