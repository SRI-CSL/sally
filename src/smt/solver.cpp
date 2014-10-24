/*
 * solver.cpp
 *
 *  Created on: Oct 24, 2014
 *      Author: dejan
 */

#include "smt/solver.h"
#include "smt/yices2.h"

#include <cassert>

using namespace sal2;
using namespace smt;

solver* factory::mk_solver(std::string id, expr::term_manager& tm) {
  solver* new_solver = 0;

  if (id == "yices2") {
    new_solver= new yices2(tm);
  } else {
    assert(false);
  }

  return new_solver;
}
