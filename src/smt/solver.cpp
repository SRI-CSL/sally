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

}
}
