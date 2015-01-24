#ifdef WITH_MATHSAT5

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

struct term_manager_with_mathsat5_test_fixture {

  term_manager tm;
  solver* mathsat5;
  options opts;

public:
  term_manager_with_mathsat5_test_fixture()
  : tm(true)
  {
    mathsat5 = factory::mk_solver("mathsat5", tm, opts);
    cout << set_tm(tm);
  }

  ~term_manager_with_mathsat5_test_fixture() {
    delete mathsat5;
  }
};

BOOST_FIXTURE_TEST_SUITE(smt_tests, term_manager_with_mathsat5_test_fixture)

BOOST_AUTO_TEST_CASE(mathsat5_basic_asserts) {

  // Assert something to mathsat5
  term_ref x = tm.mk_variable("x", tm.real_type());
  term_ref y = tm.mk_variable("y", tm.real_type());
  term_ref b = tm.mk_variable("b", tm.boolean_type());
  term_ref zero = tm.mk_rational_constant(rational());

  term_ref sum = tm.mk_term(TERM_ADD, x, y);

  // x + y <= 0
  term_ref leq = tm.mk_term(TERM_LEQ, sum, zero);

  term_ref f = tm.mk_term(TERM_AND, b, leq);

  cout << "Adding: " << f << endl;
  mathsat5->add(f, smt::solver::CLASS_A);

  solver::result result = mathsat5->check();
  cout << "Check result: " << result << endl;

  BOOST_CHECK_EQUAL(result, solver::SAT);

  term_ref g = tm.mk_term(TERM_NOT, b);

  cout << "Adding: " << g << endl;
  mathsat5->add(g, smt::solver::CLASS_A);

  result = mathsat5->check();
  cout << "Check result: " << result << endl;

  BOOST_CHECK_EQUAL(result, solver::UNSAT);

}

BOOST_AUTO_TEST_CASE(mathsat5_interpolation) {
}


BOOST_AUTO_TEST_SUITE_END()

#endif
