#ifdef WITH_MATHSAT5

#include <boost/test/unit_test.hpp>

#include "expr/term.h"
#include "expr/term_manager.h"

#include "smt/factory.h"

#include "utils/options.h"

#include <iostream>


using namespace std;
using namespace sally;
using namespace expr;
using namespace smt;

struct term_manager_with_mathsat5_test_fixture {

  term_manager tm;
  solver* mathsat5;
  options opts;

public:
  term_manager_with_mathsat5_test_fixture()
  {
    mathsat5 = factory::mk_solver("mathsat5", tm, opts);
    cout << set_tm(tm);
    cerr << set_tm(tm);
    output::trace_tag_enable("mathsat5");
  }

  ~term_manager_with_mathsat5_test_fixture() {
    output::trace_tag_disable("mathsat5");
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

  smt::solver::result result;
  term_ref interpolant;

  cout << "Checking mathsat5 interpolation" << std::endl;

  // Variables
  term_ref x = tm.mk_variable("x", tm.real_type());
  term_ref x_next = tm.mk_variable("x_next", tm.real_type());
  mathsat5->add_variable(x, smt::solver::CLASS_A);
  mathsat5->add_variable(x_next, smt::solver::CLASS_B);

  term_ref zero = tm.mk_rational_constant(rational(0, 1));
  term_ref one = tm.mk_rational_constant(rational(1, 1));
  term_ref half = tm.mk_rational_constant(rational(1, 2));

  // I: x = 0
  term_ref I = tm.mk_term(TERM_EQ, x, zero);

  // T: x_next = x + 1
  term_ref T = tm.mk_term(TERM_ADD, x, one);
  T = tm.mk_term(TERM_EQ, x_next, T);

  // G: x_next = 0.5
  term_ref G = tm.mk_term(TERM_EQ, x_next, half);

  // EXAMPLE START
  mathsat5->push();

  // The A part
  mathsat5->add(I, smt::solver::CLASS_A);
  mathsat5->add(T, smt::solver::CLASS_A);

  result = mathsat5->check();
  cout << "Check result: " << result << endl;
  BOOST_CHECK_EQUAL(result, smt::solver::SAT);

  // The B part
  mathsat5->push();
  mathsat5->add(G, smt::solver::CLASS_B);
  result = mathsat5->check();
  cout << "Check result: " << result << endl;
  BOOST_CHECK_EQUAL(result, solver::UNSAT);

  interpolant = mathsat5->interpolate();
  cout << "Interpolant: " << interpolant << endl;
  mathsat5->pop();

  // EXAMPLE END
  mathsat5->pop();

//  [1] (= state_type::next.x (+ state_type::state.x 1))
//  [2] (= state_type::state.x 0)
//  [3] (not (= state_type::state.x (/ 1 2)))
//  [4] (and (= state_type::next.x (/ (- 1) 2)) (not (>= (+ (/ (- 1) 2) (* 1 state_type::next.x)) 0)))

  // EXAMPLE START
  mathsat5->push();
  mathsat5->add(T, smt::solver::CLASS_A); // [1]
  mathsat5->add(I, smt::solver::CLASS_A); // [2]

  // [3]
  term_ref t3 = tm.mk_term(TERM_EQ, x, half);
  mathsat5->add(tm.mk_term(TERM_NOT, t3), smt::solver::CLASS_A);

  result = mathsat5->check();
  cout << "Check result: " << result << endl;
  BOOST_CHECK_EQUAL(result, smt::solver::SAT);

  mathsat5->push();

  // [4]
  term_ref half_minus = tm.mk_rational_constant(rational(-1, 2));
  term_ref t4_1 = tm.mk_term(TERM_EQ, x_next, half_minus);
  term_ref t4_2 = tm.mk_term(TERM_LT, x_next, half);
  mathsat5->add(tm.mk_term(TERM_AND, t4_1, t4_2), smt::solver::CLASS_B);
  result = mathsat5->check();
  cout << "Check result: " << result << endl;
  BOOST_CHECK_EQUAL(result, solver::UNSAT);

  interpolant = mathsat5->interpolate();
  cout << "Interpolant: " << interpolant << endl;

  mathsat5->pop();
  mathsat5->pop();
}


BOOST_AUTO_TEST_SUITE_END()

#endif
