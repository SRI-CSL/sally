/*
 * yices.cpp
 *
 *  Created on: Oct 24, 2014
 *      Author: dejan
 */

#include "smt/yices2.h"

#include "yices.h"

using namespace sal2;
using namespace smt;

yices2::yices2(expr::term_manager& tm)
: solver(tm)
{

}

yices2::~yices2() {

}

void yices2::add(const expr::term_ref& f) {

}

solver::result yices2::check() {
  return UNKNOWN;
}

expr::term_ref_strong yices2::generalize() {
  return expr::term_ref_strong();
}

void yices2::interpolate(std::vector<expr::term_ref_strong>& ) {

}
