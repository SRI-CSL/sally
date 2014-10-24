/*
 * yices.h
 *
 *  Created on: Oct 23, 2014
 *      Author: dejan
 */

#pragma once

#include "smt/solver.h"

namespace sal2 {
namespace smt {

class yices2 : public solver {
  void* yices_context;
public:
  yices2(expr::term_manager& tm);
  ~yices2();

  void add(const expr::term_ref& f);
  result check();
  expr::term_ref_strong generalize();
  void interpolate(std::vector<expr::term_ref_strong>& out);
};

}
}
