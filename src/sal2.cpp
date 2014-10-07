/*
 * sal2.cpp
 *
 *  Created on: Oct 2, 2014
 *      Author: dejan
 */

#include <iostream>
#include <iomanip>

#include "expr/term.h"
#include "expr/term_pool.h"

using namespace std;

using namespace sal2;
using namespace sal2::expr;

int main() {

  // Term manager
  term_manager tm;

  // The pool
  term_pool tmp(tm);

  // Set the term manager for output
  cout << set_tm(tm);

  // Some rationals
  rational r1(0, 1);
  rational r2(1, 1);
  rational r3(-1, 1);

  tmp.mk_term(term_constructor<OP_REAL_CONSTANT>(tm, r1, 0, 0));

}
