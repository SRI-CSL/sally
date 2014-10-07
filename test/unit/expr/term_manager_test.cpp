#include <boost/test/unit_test.hpp>

#include "expr/term.h"

#include <iostream>

using namespace std;
using namespace sal2;
using namespace expr;

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
  term_type real_type = TYPE_REAL;

  // Make some terms
  term_ref t_true = d_tm.mk_term<OP_BOOL_CONSTANT>(true);
  cout << t_true << endl;
  BOOST_CHECK_EQUAL(d_tm.term_of(t_true).size(), 0);

  term_ref t_false = d_tm.mk_term<OP_BOOL_CONSTANT>(false);
  cout << t_false << endl;
  BOOST_CHECK_EQUAL(d_tm.term_of(t_false).size(), 0);

  // A variable
  term_ref t_v_bool = d_tm.mk_term<OP_VARIABLE>(bool_type);
  cout << t_v_bool << endl;
  BOOST_CHECK_EQUAL(d_tm.term_of(t_v_bool).size(), 0);

  // Unary
  term_ref t_not = d_tm.mk_term<OP_NOT>(t_v_bool);
  cout << t_not << endl;
  BOOST_CHECK_EQUAL(d_tm.term_of(t_not).size(), 1);

  // Binary
  term_ref t_or = d_tm.mk_term<OP_OR>(t_v_bool, t_not);
  cout << t_or << endl;
  BOOST_CHECK_EQUAL(d_tm.term_of(t_or).size(), 2);

  std::vector<term_ref> children;
  children.push_back(t_true);
  children.push_back(t_false);
  children.push_back(t_v_bool);
  children.push_back(t_not);
  children.push_back(t_or);
  term_ref t_and = d_tm.mk_term<OP_AND>(children.begin(), children.end());
  cout << t_and << endl;
  BOOST_CHECK_EQUAL(d_tm.term_of(t_and).size(), 5);

  term_ref t_v_real_0 = d_tm.mk_term<OP_VARIABLE>(real_type);
  cout << t_v_real_0 << endl;
  term_ref t_v_real_1 = d_tm.mk_term<OP_VARIABLE>(real_type);
  cout << t_v_real_1 << endl;
  term_ref t_v_real_2 = d_tm.mk_term<OP_VARIABLE>(real_type);
  cout << t_v_real_2 << endl;

  term_ref t_r0 = d_tm.mk_term<OP_REAL_CONSTANT>(rational(0, 1));
  cout << t_r0 << endl;
  term_ref t_r1 = d_tm.mk_term<OP_REAL_CONSTANT>(rational(1, 2));
  cout << t_r1 << endl;
  term_ref t_r2 = d_tm.mk_term<OP_REAL_CONSTANT>(rational(-1, 2));
  cout << t_r2 << endl;

  term_ref t_sub = d_tm.mk_term<OP_SUB>(t_v_real_0, t_v_real_1);
  cout << t_sub << endl;
  BOOST_CHECK_EQUAL(d_tm.term_of(t_sub).size(), 2);
  term_ref t_div = d_tm.mk_term<OP_DIV>(t_v_real_1, t_v_real_2);
  cout << t_div << endl;
  BOOST_CHECK_EQUAL(d_tm.term_of(t_div).size(), 2);

  term_ref t_add_children[] = { t_v_real_0, t_v_real_1, t_r1 };
  term_ref t_add = d_tm.mk_term<OP_ADD>(t_add_children, t_add_children + 3);
  cout << t_add << endl;
  const term& add = d_tm.term_of(t_add);
  BOOST_CHECK_EQUAL(add.size(), 3);
  for (unsigned i = 0; i < add.size(); ++ i) {
    BOOST_CHECK_EQUAL(add[i], t_add_children[i]);
  }

  term_ref t_mul_children[] = { t_v_real_1, t_r1, t_v_real_2, t_r2 };
  term_ref t_mul = d_tm.mk_term<OP_MUL>(t_mul_children, t_mul_children + 4);
  cout << t_mul << endl;
  const term& mul = d_tm.term_of(t_mul);
  BOOST_CHECK_EQUAL(mul.size(), 4);
  for (unsigned i = 0; i < mul.size(); ++ i) {
    BOOST_CHECK_EQUAL(mul[i], t_mul_children[i]);
  }
}

BOOST_AUTO_TEST_SUITE_END();
