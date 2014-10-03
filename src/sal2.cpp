/*
 * sal2.cpp
 *
 *  Created on: Oct 2, 2014
 *      Author: dejan
 */

#include <iostream>
#include <iomanip>

#include <expr/term.h>

using namespace std;

using namespace sal2;
using namespace sal2::term;

int main() {

  // Term manager
  term_manager tm;

  // Set the term manager for output
  cout << set_tm(tm);

  // Some types
  term_type bool_type = TYPE_BOOL;

  // Make some terms
  term_ref t_true = tm.mk_term<OP_BOOL_CONSTANT>(true);
  cout << t_true << endl;

  term_ref t_false = tm.mk_term<OP_BOOL_CONSTANT>(false);
  cout << t_false << endl;

  // A variable
  term_ref t_var = tm.mk_term<OP_VARIABLE>(bool_type);
  cout << t_var << endl;

  // Unary
  term_ref t_not = tm.mk_term(OP_NOT, t_var);
  cout << t_not << endl;

  // Binary
  term_ref t_or = tm.mk_term(OP_OR, t_var, t_not);
  cout << t_or << endl;

  std::vector<term_ref> children;
  children.push_back(t_true);
  children.push_back(t_false);
  children.push_back(t_var);
  children.push_back(t_not);
  children.push_back(t_or);
  term_ref t_and = tm.mk_term(OP_AND, children);

  cout << t_and << endl;
}
