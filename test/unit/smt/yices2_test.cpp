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

BOOST_AUTO_TEST_CASE(basic_asserts) {

  // Assert something to yices
  term_ref x = tm.mk_variable("x", tm.realType());
  term_ref y = tm.mk_variable("y", tm.realType());
  term_ref b = tm.mk_variable("b", tm.booleanType());
  term_ref zero = tm.mk_rational_constant(rational());

  term_ref sum = tm.mk_term(TERM_ADD, x, y);

  // x + y <= 0
  term_ref leq = tm.mk_term(TERM_LEQ, sum, zero);

  term_ref f = tm.mk_term(TERM_AND, b, leq);

  cout << "Adding: " << f << endl;
  yices2->add(f);

  solver::result result = yices2->check();
  cout << "Check result: " << result << endl;

  BOOST_CHECK_EQUAL(result, solver::SAT);

  term_ref g = tm.mk_term(TERM_NOT, b);

  cout << "Adding: " << g << endl;
  yices2->add(g);

  result = yices2->check();
  cout << "Check result: " << result << endl;

  BOOST_CHECK_EQUAL(result, solver::UNSAT);

}

BOOST_AUTO_TEST_CASE(generalization) {

  // Assert something to yices
  term_ref x = tm.mk_variable("x", tm.realType());
  term_ref y = tm.mk_variable("y", tm.realType());
  term_ref z = tm.mk_variable("z", tm.realType());
  term_ref zero = tm.mk_rational_constant(rational());

  term_ref sum_x_y = tm.mk_term(TERM_ADD, x, y);
  term_ref sum_x_y_z = tm.mk_term(TERM_ADD, sum_x_y, z);

  // x + y <= 0
  term_ref leq_x_y = tm.mk_term(TERM_LEQ, sum_x_y, zero);
  // 0 <= x + y
  term_ref geq_x_y = tm.mk_term(TERM_LEQ, zero, sum_x_y);
  // 0 <= x + y + z
  term_ref geq_x_y_z = tm.mk_term(TERM_LEQ, zero, sum_x_y_z);

  output::set_verbosity(std::cerr, 10);
  output::set_verbosity(std::cout, 10);

  // Add and check
  yices2->add(leq_x_y);
  yices2->add(geq_x_y);
  yices2->add(geq_x_y_z);
  solver::result result = yices2->check();
  cout << "Check result: " << result << endl;

  // Generalize
  std::vector<term_ref> to_elim;
  to_elim.push_back(y);
  yices2->generalize(to_elim);
}


BOOST_AUTO_TEST_SUITE_END()
