#include <boost/test/unit_test.hpp>

#include "expr/term.h"

#include <iostream>

using namespace std;
using namespace sal2;
using namespace term;

struct term_manager_test_fixture {
  term_manager d_tm;
public:
  term_manager_test_fixture() {}
  ~term_manager_test_fixture() {}
};

BOOST_FIXTURE_TEST_SUITE(term_manager_test, term_manager_test_fixture);

BOOST_AUTO_TEST_CASE(mk_term) {

  // Set the term manager for output
  cout << set_tm(d_tm);

  // Some types
  term_type bool_type = TYPE_BOOL;

  // Make some terms
  term_ref t_true = d_tm.mk_term<OP_BOOL_CONSTANT>(true);
  cout << t_true << endl;

  term_ref t_false = d_tm.mk_term<OP_BOOL_CONSTANT>(false);
  cout << t_false << endl;

  // A variable
  term_ref t_var = d_tm.mk_term<OP_VARIABLE>(bool_type);
  cout << t_var << endl;

  // Unary
  term_ref t_not = d_tm.mk_term<OP_NOT>(t_var);
  cout << t_not << endl;

  // Binary
  term_ref t_or = d_tm.mk_term<OP_OR>(t_var, t_not);
  cout << t_or << endl;

  std::vector<term_ref> children;
  children.push_back(t_true);
  children.push_back(t_false);
  children.push_back(t_var);
  children.push_back(t_not);
  children.push_back(t_or);
  term_ref t_and = d_tm.mk_term<OP_AND>(children.begin(), children.end());

  cout << t_and << endl;
}

BOOST_AUTO_TEST_SUITE_END();
