#include <boost/test/unit_test.hpp>

#include "smt/solver.h"

#include <iostream>

using namespace std;
using namespace sal2;
using namespace expr;

struct term_manager_test_fixture {

  term_manager tm;
  smt::solver* yices2;

public:
  term_manager_test_fixture()
  : tm(true)
  {
    yices2 = smt::factory::mk_solver("yices2", tm);
  }

  ~term_manager_test_fixture() {
    delete yices2;
  }
};

BOOST_FIXTURE_TEST_SUITE(term_manager_construction, term_manager_test_fixture)

BOOST_AUTO_TEST_CASE(basic_asserts) {
  // Assert something to yices
}

BOOST_AUTO_TEST_SUITE_END()
