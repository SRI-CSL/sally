/*
 * solver.cpp
 *
 *  Created on: Oct 24, 2014
 *      Author: dejan
 */

#include "smt/solver.h"
#include "smt/yices2.h"

#include <cassert>
#include <iostream>

namespace sal2 {
namespace smt {

solver* factory::mk_solver(std::string id, expr::term_manager& tm) {
  solver* new_solver = 0;

  if (id == "yices2") {
    new_solver= new yices2(tm);
  } else {
    assert(false);
  }

  return new_solver;
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
