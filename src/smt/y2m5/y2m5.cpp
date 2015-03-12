/*
 * yices.cpp
 *
 *  Created on: Oct 24, 2014
 *      Author: dejan
 */

#ifdef WITH_YICES2
#ifdef WITH_MATHSAT5

#include <iostream>

#include "expr/term.h"
#include "expr/term_manager.h"
#include "expr/rational.h"
#include "smt/y2m5/y2m5.h"
#include "smt/yices2/yices2.h"
#include "smt/mathsat5/mathsat5.h"
#include "utils/trace.h"
#include "smt/incremental_wrapper.h"
#include "smt/delayed_wrapper.h"
#include "smt/factory.h"

namespace sally {
namespace smt {

size_t y2m5::s_instance = 0;

class mathsat_constructor : public solver_constructor {
  expr::term_manager& d_tm;
  const options& d_opts;
public:
  mathsat_constructor(expr::term_manager& tm, const options& opts)
  : d_tm(tm), d_opts(opts) {}
  ~mathsat_constructor() {};
  solver* mk_solver() { return factory::mk_solver("mathsat5", d_tm, d_opts); }
};

y2m5::y2m5(expr::term_manager& tm, const options& opts)
: solver("y2m5", tm, opts)
, d_last_mathsat5_result(UNKNOWN)
, d_last_yices2_result(UNKNOWN)
{
  d_yices2 = factory::mk_solver("yices2", tm, opts);
  if (opts.get_bool("y2m5-mathsat5-flatten")) {
    solver_constructor* constructor = new mathsat_constructor(tm, opts);
    d_mathsat5 = new incremental_wrapper("mathsat5_nonincremental", tm, opts, constructor);
  } else {
    d_mathsat5 = new delayed_wrapper("mathsat5_incremental", tm, opts, factory::mk_solver("mathsat5", tm, opts));
  }
  s_instance ++;
}

y2m5::~y2m5() {
  delete d_mathsat5;
  delete d_yices2;
  s_instance --;
}

void y2m5::add(expr::term_ref f, formula_class f_class) {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: adding " << f << std::endl;
  d_yices2->add(f, f_class);
  d_mathsat5->add(f, f_class);
  d_last_mathsat5_result = UNKNOWN;
  d_last_yices2_result = UNKNOWN;
}

solver::result y2m5::check() {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: check()" << std::endl;
  d_last_yices2_result = d_yices2->check();
  d_last_mathsat5_result = UNKNOWN;
  return d_last_yices2_result;
}

void y2m5::get_model(expr::model& m) const {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: get_model()" << std::endl;
  assert(d_last_yices2_result == SAT);
  d_yices2->get_model(m);
}

void y2m5::push() {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: push()" << std::endl;
  d_yices2->push();
  d_mathsat5->push();
  d_last_mathsat5_result = UNKNOWN;
  d_last_yices2_result = UNKNOWN;
}

void y2m5::pop() {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: pop()" << std::endl;
  d_yices2->pop();
  d_mathsat5->pop();
  d_last_mathsat5_result = UNKNOWN;
  d_last_yices2_result = UNKNOWN;
}


void y2m5::generalize(std::vector<expr::term_ref>& out) {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: generalizing" << std::endl;
  assert(d_last_yices2_result == SAT);
  d_yices2->generalize(out);
}

void y2m5::interpolate(std::vector<expr::term_ref>& out) {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: interpolating" << std::endl;
  if (d_last_mathsat5_result == UNKNOWN) {
    d_last_mathsat5_result = d_mathsat5->check();
  }
  if (d_last_mathsat5_result != UNSAT) {
    // Check the model for correctness
    d_mathsat5->check_model();
  }
  assert(d_last_mathsat5_result == UNSAT);
  d_mathsat5->interpolate(out);
}

void y2m5::get_unsat_core(std::vector<expr::term_ref>& out) {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: unsat core" << std::endl;
  if (d_last_mathsat5_result == UNKNOWN) {
    d_last_mathsat5_result = d_mathsat5->check();
  }
  assert(d_last_mathsat5_result == UNSAT);
  d_mathsat5->get_unsat_core(out);
}

void y2m5::add_x_variable(expr::term_ref x_var) {
  solver::add_x_variable(x_var);
  d_yices2->add_x_variable(x_var);
  d_mathsat5->add_x_variable(x_var);
}

void y2m5::add_y_variable(expr::term_ref y_var) {
  solver::add_y_variable(y_var);
  d_yices2->add_y_variable(y_var);
  d_mathsat5->add_y_variable(y_var);
}


bool y2m5::supports(feature f) const {
  switch (f) {
  case GENERALIZATION:
    return d_yices2->supports(f);
  case INTERPOLATION:
    return d_mathsat5->supports(f);
  case UNSAT_CORE:
    return d_mathsat5->supports(f);
  default:
    return false;
  }
}

}
}

#endif
#endif
