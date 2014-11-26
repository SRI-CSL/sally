/*
 * solver.cpp
 *
 *  Created on: Oct 24, 2014
 *      Author: dejan
 */

#include "smt/solver.h"
#include "smt/yices2.h"
#include "smt/smt2_solver.h"

#include <cassert>
#include <iostream>

namespace sal2 {
namespace smt {

solver* factory::mk_solver(std::string id, expr::term_manager& tm) {
  if (id == "yices2") {
    return new yices2(tm);
  }
  if (id == "smt2_solver") {
    return new smt2_solver(tm);
  }

  assert(false);
  return 0;
}

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

}
}
