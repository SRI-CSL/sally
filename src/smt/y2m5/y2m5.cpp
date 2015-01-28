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

#define unused_var(x) { (void) x; }

namespace sal2 {
namespace smt {

size_t y2m5::s_instance = 0;

y2m5::y2m5(expr::term_manager& tm, const options& opts)
: solver("y2m5", tm, opts)
{
  d_yices2 = new yices2(tm, opts);
  d_mathsat5 = new mathsat5(tm, opts);
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
}

solver::result y2m5::check() {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: check()" << std::endl;
  result yices2_result = d_yices2->check();
  return yices2_result;
}

void y2m5::get_model(expr::model& m) const {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: get_model()" << std::endl;
  d_yices2->get_model(m);
}

void y2m5::push() {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: push()" << std::endl;
  d_yices2->push();
  d_mathsat5->push();
}

void y2m5::pop() {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: pop()" << std::endl;
  d_yices2->pop();
  d_mathsat5->pop();
}


void y2m5::generalize(std::vector<expr::term_ref>& out) {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: generalizing" << std::endl;
  d_yices2->generalize(out);
}

void y2m5::interpolate(std::vector<expr::term_ref>& out) {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: interpolating" << std::endl;
  result mathsat5_result  = d_mathsat5->check();
  unused_var(mathsat5_result);
  assert(mathsat5_result == UNSAT);
  d_mathsat5->interpolate(out);
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


}
}

#endif
#endif
