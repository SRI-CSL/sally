#ifdef WITH_YICES2

#include <boost/test/unit_test.hpp>

#include "expr/term.h"
#include "expr/term_manager.h"

#include "smt/factory.h"

#include "utils/options.h"

#include <iostream>


using namespace std;
using namespace sal2;
using namespace expr;
using namespace smt;

struct term_manager_with_yices_test_fixture {

  term_manager tm;
  solver* yices2;
  options opts;

public:
  term_manager_with_yices_test_fixture()
  : tm(true)
  {
    yices2 = factory::mk_solver("yices2", tm, opts);
    cout << set_tm(tm);
  }

  ~term_manager_with_yices_test_fixture() {
    delete yices2;
  }
};

BOOST_FIXTURE_TEST_SUITE(smt_tests, term_manager_with_yices_test_fixture)

BOOST_AUTO_TEST_CASE(yices2_basic_asserts) {

  // Assert something to yices
  term_ref x = tm.mk_variable("x", tm.real_type());
  term_ref y = tm.mk_variable("y", tm.real_type());
  term_ref b = tm.mk_variable("b", tm.boolean_type());
  term_ref zero = tm.mk_rational_constant(rational());

  term_ref sum = tm.mk_term(TERM_ADD, x, y);

  // x + y <= 0
  term_ref leq = tm.mk_term(TERM_LEQ, sum, zero);

  term_ref f = tm.mk_term(TERM_AND, b, leq);

  cout << "Adding: " << f << endl;
  yices2->add(f, smt::solver::CLASS_A);

  solver::result result = yices2->check();
  cout << "Check result: " << result << endl;

  BOOST_CHECK_EQUAL(result, solver::SAT);

  term_ref g = tm.mk_term(TERM_NOT, b);

  cout << "Adding: " << g << endl;
  yices2->add(g, smt::solver::CLASS_A);

  result = yices2->check();
  cout << "Check result: " << result << endl;

  BOOST_CHECK_EQUAL(result, solver::UNSAT);

}

BOOST_AUTO_TEST_CASE(yices2_generalization) {

  yices2->push();

  // Assert something to yices
  term_ref x = tm.mk_variable("x", tm.real_type());
  term_ref y = tm.mk_variable("y", tm.real_type());
  term_ref z = tm.mk_variable("z", tm.real_type());
  term_ref zero = tm.mk_rational_constant(rational());

  expr::term_ref G;

  term_ref sum_x_y = tm.mk_term(TERM_ADD, x, y);
  term_ref sum_x_y_z = tm.mk_term(TERM_ADD, sum_x_y, z);

  // x + y <= 0
  term_ref leq_x_y = tm.mk_term(TERM_LEQ, sum_x_y, zero);
  // 0 <= x + y
  term_ref geq_x_y = tm.mk_term(TERM_LEQ, zero, sum_x_y);

  // Add and check
  yices2->add(leq_x_y, smt::solver::CLASS_A);
  yices2->add(geq_x_y, smt::solver::CLASS_A);

  // Check and generalize
  solver::result result = yices2->check();
  cout << "Check result: " << result << endl;

  // Generalize
  G = yices2->generalize();
  cout << "G: " << G << endl;

  // 0 <= x + y + z
  term_ref geq_x_y_z = tm.mk_term(TERM_LEQ, zero, sum_x_y_z);

  // Add some more
  yices2->add(geq_x_y_z, smt::solver::CLASS_B);

  // Check and generalize
  result = yices2->check();
  cout << "Check result: " << result << endl;
  G = yices2->generalize();
  cout << "G: " << G << endl;

  yices2->pop();

  term_ref b1 = tm.mk_variable("b1", tm.boolean_type());
  term_ref b2 = tm.mk_variable("b2", tm.boolean_type());

  term_ref imp1 = tm.mk_term(expr::TERM_IMPLIES, b1, geq_x_y_z);
  term_ref imp2 = tm.mk_term(expr::TERM_IMPLIES, b2, leq_x_y);

  yices2->add(imp1, smt::solver::CLASS_B);
  yices2->add(imp2, smt::solver::CLASS_B);

  yices2->add_y_variable(b1);

  result = yices2->check();
  cout << "Check result: " << result << endl;

  G = yices2->generalize();
  cout << "G: " << G << endl;

}


BOOST_AUTO_TEST_SUITE_END()

#endif
