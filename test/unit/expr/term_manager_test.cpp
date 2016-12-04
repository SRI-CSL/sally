#include <boost/test/unit_test.hpp>

#include "expr/term.h"
#include "expr/term_manager.h"

#include "utils/statistics.h"

#include <iostream>

using namespace std;
using namespace sally;
using namespace expr;

struct term_manager_test_fixture {

  utils::statistics stats;
  term_manager tm;

public:
  term_manager_test_fixture()
  : tm(stats)
  {}

  ~term_manager_test_fixture() {
    cout << tm << endl;
  }
};

BOOST_FIXTURE_TEST_SUITE(term_manager_tests, term_manager_test_fixture)

BOOST_AUTO_TEST_CASE(tuple) {

  // Set term manager for output
  cout << set_tm(tm);

  // Tuple arguments
  term_ref t0 = tm.real_type();
  term_ref t1 = tm.integer_type();

  // Construct and output
  std::vector<term_ref> args;
  args.push_back(t0);
  args.push_back(t1);
  term_ref tuple_type = tm.tuple_type(args);
  cout << tuple_type << endl;
  args.clear();

  // Access the tuple type arguments
  term_ref t0_access = tm.get_tuple_type_element(tuple_type, 0);
  term_ref t1_access = tm.get_tuple_type_element(tuple_type, 1);
  BOOST_CHECK_EQUAL(t0, t0_access);
  BOOST_CHECK_EQUAL(t1, t1_access);

  // Make a constant and test access and write
  term_ref c1 = tm.mk_rational_constant(rational(1, 2));
  term_ref c2 = tm.mk_rational_constant(rational(1, 1));
  args.push_back(c1);
  args.push_back(c2);
  term_ref tuple = tm.mk_tuple(args);
  cout << tuple << endl;
  term_ref tuple_type_new = tm.type_of(tuple);
  cout << tuple_type_new << endl;

  term_ref read0 = tm.mk_tuple_read(tuple, 0);
  term_ref read1 = tm.mk_tuple_read(tuple, 1);
  term_ref write0 = tm.mk_tuple_write(tuple, 0, c1);
  term_ref write1 = tm.mk_tuple_write(tuple, 1, c1);
  cout << read0 << " : " << tm.type_of(read0) << endl;
  cout << read1 << " : " << tm.type_of(read1) << endl;
  cout << write0 << " : " << tm.type_of(write0) << endl;
  cout << write1 << " : " << tm.type_of(write0) << endl;
}

BOOST_AUTO_TEST_CASE(function_and_lambda) {

  // Set term manager for output
  cout << set_tm(tm);

  // Tuple arguments
  term_ref t0 = tm.real_type();
  term_ref t1 = tm.integer_type();
  term_ref t2 = tm.boolean_type();
  std::vector<term_ref> args;
  args.push_back(t0);
  args.push_back(t1);
  args.push_back(t2);
  term_ref fun = tm.function_type(args);
  args.clear();
  cout << "function type: " << fun << endl;

  // Make a lambda
  term_ref x0 = tm.mk_variable(t0);
  term_ref x1 = tm.mk_variable(t1);
  args.clear(); args.push_back(x0); args.push_back(x1);
  term_ref body = tm.mk_term(TERM_LT, x0, x1);
  term_ref lambda = tm.mk_lambda(args, body);
  term_ref lambda_type = tm.type_of(lambda);
  cout << "lambda: " << lambda << endl;
  cout << "lambda_type: " << lambda_type << endl;

  BOOST_CHECK_EQUAL(fun, lambda_type);
}

BOOST_AUTO_TEST_CASE(quantifiers) {

  std::vector<term_ref> args;

  // Set term manager for output
  cout << set_tm(tm);

  // Make a quantifier
  term_ref x0 = tm.mk_variable(tm.real_type());
  term_ref x1 = tm.mk_variable(tm.integer_type());
  term_ref x2 = tm.mk_variable(tm.integer_type());
  term_ref body = tm.mk_term(TERM_LT, x0, tm.mk_term(TERM_ADD, x1, x2));
  cout << "body: " << body << endl;
  args.clear(); args.push_back(x1); args.push_back(x2);
  body = tm.mk_exists(args, body);
  cout << "body: " << body << endl;
  args.clear(); args.push_back(x0);
  term_ref quantifier = tm.mk_forall(args, body);
  term_ref quantifier_type = tm.type_of(quantifier);

  cout << "quantifier: " << quantifier << endl;
  cout << "quantifier type: " << quantifier_type << endl;

  BOOST_CHECK_EQUAL(quantifier_type, tm.boolean_type());
}

BOOST_AUTO_TEST_CASE(arrays) {

  // Set term manager for output
  cout << set_tm(tm);

  // Make array type
  term_ref index_type = tm.boolean_type();
  term_ref element_type = tm.real_type();
  term_ref array_type = tm.array_type(index_type, element_type);
  cout << array_type;

  // Make array read
  term_ref a = tm.mk_variable("a", array_type);
  term_ref t = tm.mk_boolean_constant(true);
  term_ref aread = tm.mk_array_read(a, t);
  term_ref aread_type = tm.type_of(aread);
  cout << "array read: " << aread << endl;
  cout << "array read type: " << aread_type << endl;
  BOOST_CHECK_EQUAL(element_type, aread_type);

  // Make array write
  term_ref f = tm.mk_boolean_constant(false);
  term_ref zero = tm.mk_rational_constant(rational(0, 1));
  term_ref awrite = tm.mk_array_write(a, f, zero);
  term_ref awrite_type = tm.type_of(awrite);
  cout << "array write: " << awrite << endl;
  cout << "array write type:" << awrite_type << endl;
  BOOST_CHECK_EQUAL(awrite_type, array_type);

}

BOOST_AUTO_TEST_CASE(predicate_sybtype) {

  // Set term manager for output
  cout << set_tm(tm);

  // Make array type
  term_ref base_type = tm.real_type();
  term_ref x = tm.mk_variable(base_type);
  term_ref predicate = tm.mk_term(TERM_LEQ, x, tm.mk_rational_constant(rational(100, 1)));
  term_ref type = tm.mk_predicate_subtype(x, predicate);
  cout << "predicate_type: " << type << endl;
  x = tm.mk_variable(type);
  predicate = tm.mk_term(TERM_GEQ, x, tm.mk_rational_constant(rational(0, 1)));
  type = tm.mk_predicate_subtype(x, predicate);
  cout << "predicate_type: " << type << endl;

}


BOOST_AUTO_TEST_CASE(mk_term) {

  // Set the term manager for output
  cout << set_tm(tm);

  // Make some terms
  term_ref t_true = tm.mk_boolean_constant(true);
  cout << t_true << endl;
  BOOST_CHECK_EQUAL(tm.term_of(t_true).size(), 0);

  term_ref t_false = tm.mk_boolean_constant(false);
  cout << t_false << endl;
  BOOST_CHECK_EQUAL(tm.term_of(t_false).size(), 0);

  // A variable
  term_ref t_v_bool = tm.mk_variable("x", tm.boolean_type());
  cout << t_v_bool << endl;
  BOOST_CHECK_EQUAL(tm.term_of(t_v_bool).size(), 1);

  // Unary
  term_ref t_not = tm.mk_term(TERM_NOT, t_v_bool);
  cout << t_not << endl;
  BOOST_CHECK_EQUAL(tm.term_of(t_not).size(), 1);

  // Binary
  term_ref t_or = tm.mk_term(TERM_OR, t_v_bool, t_not);
  cout << t_or << endl;
  BOOST_CHECK_EQUAL(tm.term_of(t_or).size(), 2);

  std::vector<term_ref> children;
  children.push_back(t_true);
  children.push_back(t_false);
  children.push_back(t_v_bool);
  children.push_back(t_not);
  children.push_back(t_or);
  term_ref t_and = tm.mk_term(TERM_AND, children);
  cout << t_and << endl;
  BOOST_CHECK_EQUAL(tm.term_of(t_and).size(), 5);

  term_ref t_v_real_0 = tm.mk_variable("x", tm.real_type());
  cout << t_v_real_0 << endl;
  term_ref t_v_real_1 = tm.mk_variable("y", tm.real_type());
  cout << t_v_real_1 << endl;
  term_ref t_v_real_2 = tm.mk_variable("z", tm.real_type());
  cout << t_v_real_2 << endl;

  term_ref t_r0 = tm.mk_rational_constant(rational(0, 1));
  cout << t_r0 << endl;
  term_ref t_r1 = tm.mk_rational_constant(rational(1, 2));
  cout << t_r1 << endl;
  term_ref t_r2 = tm.mk_rational_constant(rational(-1, 2));
  cout << t_r2 << endl;

  term_ref t_sub = tm.mk_term(TERM_SUB, t_v_real_0, t_v_real_1);
  cout << t_sub << endl;
  BOOST_CHECK_EQUAL(tm.term_of(t_sub).size(), 2);
  term_ref t_div = tm.mk_term(TERM_DIV, t_v_real_1, t_v_real_2);
  cout << t_div << endl;
  BOOST_CHECK_EQUAL(tm.term_of(t_div).size(), 2);

  term_ref t_add_children[] = { t_v_real_0, t_v_real_1, t_r1 };
  term_ref t_add = tm.mk_term(TERM_ADD, t_add_children, t_add_children + 3);
  cout << t_add << endl;
  const term& add = tm.term_of(t_add);
  BOOST_CHECK_EQUAL(add.size(), 3);
  for (unsigned i = 0; i < add.size(); ++ i) {
    BOOST_CHECK_EQUAL(add[i], t_add_children[i]);
  }

  term_ref t_mul_children[] = { t_v_real_1, t_r1, t_v_real_2, t_r2 };
  term_ref t_mul = tm.mk_term(TERM_MUL, t_mul_children, 4);
  cout << t_mul << endl;
  const term& mul = tm.term_of(t_mul);
  BOOST_CHECK_EQUAL(mul.size(), 4);
  for (unsigned i = 0; i < mul.size(); ++ i) {
    BOOST_CHECK_EQUAL(mul[i], t_mul_children[i]);
  }
}

BOOST_AUTO_TEST_CASE(term_manager_hashconsing) {

  const int n = 10;

  // Set the term manager for output
  cout << set_tm(tm);

  // Some rationals
  rational number[n];
  for (int i = 0; i < n; ++ i) {
    number[i] = rational(i, i + 1);
  }

  term_ref number_ref[2][n];
  for (int k = 0; k < 2; ++ k) {
    for (int i = 0; i < n; ++ i) {
      term_ref ref = tm.mk_rational_constant(number[i]);
      number_ref[k][i] = ref;
      cout << ref << endl;
    }
  }

  for (int i = 0; i < n; ++ i) {
    if (i > 0) {
      BOOST_CHECK_NE(number_ref[0][i-1], number_ref[0][i]);
    }
    BOOST_CHECK_EQUAL(number_ref[0][i], number_ref[0][i]);
  }

  term_ref_strong add_ref[2][n];
  for (int k = 0; k < 2; ++ k) {
    for (int i = 1; i < n; ++ i) {
      term_ref ref = tm.mk_term(TERM_ADD, number_ref[k] + 0, number_ref[k] + i + 1);
      add_ref[k][i] = term_ref_strong(tm, ref);
    }
  }

  for (int i = 1; i < n; ++ i) {
    if (i > 2) {
      BOOST_CHECK_NE(add_ref[0][i-1], add_ref[0][i]);
    }
    BOOST_CHECK_EQUAL(add_ref[0][i], add_ref[1][i]);
  }

  cout << "Term manager pre-destructor: " << tm << endl;

}

BOOST_AUTO_TEST_SUITE_END()
