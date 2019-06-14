#ifdef WITH_DREAL

#include <boost/test/unit_test.hpp>

#include "expr/term.h"
#include "expr/term_manager.h"

#include "smt/factory.h"

#include "utils/options.h"
#include "utils/statistics.h"

#include <iostream>


using namespace std;
using namespace sally;
using namespace expr;
using namespace smt;

struct term_manager_with_dreal_test_fixture {

  utils::statistics stats;
  term_manager tm;
  solver* dreal;
  options opts;

public:

  term_manager_with_dreal_test_fixture()
  : tm(stats)
  {
    dreal = factory::mk_solver("dreal", tm, opts, stats);
    cout << set_tm(tm);
    cerr << set_tm(tm);
    output::trace_tag_enable("dreal");
  }

  ~term_manager_with_dreal_test_fixture() {
    output::trace_tag_disable("dreal");
    delete dreal;
  }
};

BOOST_FIXTURE_TEST_SUITE(smt_tests, term_manager_with_dreal_test_fixture)

BOOST_AUTO_TEST_CASE(dreal_basic_asserts) {

  // Assert something to dreal
  term_ref x = tm.mk_variable("x", tm.real_type());
  term_ref y = tm.mk_variable("y", tm.real_type());
  term_ref b = tm.mk_variable("b", tm.boolean_type());

  dreal->add_variable(x, smt::solver::CLASS_A);
  dreal->add_variable(y, smt::solver::CLASS_A);
  dreal->add_variable(b, smt::solver::CLASS_A);

  term_ref zero = tm.mk_rational_constant(rational());

  term_ref sum = tm.mk_term(TERM_ADD, x, y);

  // x + y <= 0
  term_ref leq = tm.mk_term(TERM_LEQ, sum, zero);

  term_ref f = tm.mk_term(TERM_AND, b, leq);


  cout << "Adding: " << f << endl;
  dreal->add(f, smt::solver::CLASS_A);

  solver::result result = dreal->check();
  cout << "Check result: " << result << endl;

  BOOST_CHECK_EQUAL(result, solver::SAT);

  term_ref g = tm.mk_term(TERM_NOT, b);

  cout << "Adding: " << g << endl;
  dreal->add(g, smt::solver::CLASS_A);

  result = dreal->check();
  cout << "Check result: " << result << endl;

  BOOST_CHECK_EQUAL(result, solver::UNSAT);

}

BOOST_AUTO_TEST_SUITE_END()

#endif
