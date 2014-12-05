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

expr::term_ref solver::generalize(const std::vector<expr::term_ref>& to_eliminate) {
  std::vector<expr::term_ref> projection_out;
  generalize(to_eliminate, projection_out);
  if (projection_out.size() == 0) {
    return d_tm.mk_boolean_constant(true);
  }
  if (projection_out.size() == 1) {
    return projection_out[0];
  }
  return d_tm.mk_term(expr::TERM_AND, projection_out);
}

}
}
