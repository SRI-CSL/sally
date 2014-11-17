/*
 * yices.cpp
 *
 *  Created on: Oct 24, 2014
 *      Author: dejan
 */

#include "expr/term.h"
#include "expr/term_manager.h"

#include <boost/unordered_map.hpp>

#include "smt/yices2.h"

#include "yices.h"

namespace sal2 {
namespace smt {

class yices2_internal {

  expr::term_manager& d_tm;

  static int instances;

  type_t d_bool_type;
  type_t d_int_type;
  type_t d_real_type;

  context_t *d_ctx;

  std::vector<expr::term_ref_strong> d_assertions;

  typedef boost::unordered_map<expr::term_ref, term_t, expr::term_ref_hasher> term_cache;

  term_cache d_term_cache;

public:

  yices2_internal(expr::term_manager& tm);
  ~yices2_internal();

  term_t to_yices2_term(expr::term_ref ref);
  type_t to_yices2_type(expr::term_ref ref);

  term_t mk_yices2_term(expr::term_op op, size_t n, term_t* children);

  void add(expr::term_ref ref);
  solver::result check();
};

int yices2_internal::instances = 0;

yices2_internal::yices2_internal(expr::term_manager& tm)
: d_tm(tm)
{
  // Initialize
  if (instances == 0) {
    yices_init();
    instances ++;
  }

  // The basic types
  d_bool_type = yices_bool_type();
  d_int_type = yices_int_type();
  d_real_type = yices_real_type();

  // The context
  d_ctx = yices_new_context(NULL);
}

yices2_internal::~yices2_internal() {

  // The context
  yices_free_context(d_ctx);

  // Cleanup if the last one
  instances--;
  if (instances == 0) {
    yices_exit();
  }
}

term_t yices2_internal::mk_yices2_term(expr::term_op op, size_t n, term_t* children) {
  term_t result = NULL_TERM;

  switch (op) {
  case expr::TERM_AND:
    result = yices_and(n, children);
    break;
  case expr::TERM_OR:
    result = yices_or(n, children);
    break;
  case expr::TERM_NOT:
    assert(n == 1);
    result = yices_not(children[0]);
    break;
  case expr::TERM_IMPLIES:
    assert(n == 2);
    result = yices_implies(children[0], children[1]);
    break;
  case expr::TERM_XOR:
    result = yices_xor(n, children);
    break;
  case expr::TERM_ADD:
    result = yices_sum(n, children);
    break;
  case expr::TERM_SUB:
    assert(n == 2);
    result = yices_sub(children[0], children[1]);
    break;
  case expr::TERM_MUL:
    result = yices_product(n, children);
    break;
  case expr::TERM_DIV:
    result = yices_division(children[0], children[1]);
    break;
  case expr::TERM_LEQ:
    assert(n == 2);
    result = yices_arith_leq_atom(children[0], children[1]);
    break;
  case expr::TERM_LT:
    assert(n == 2);
    result = yices_arith_lt_atom(children[0], children[1]);
    break;
  case expr::TERM_GEQ:
    assert(n == 2);
    result = yices_arith_geq_atom(children[0], children[1]);
    break;
  case expr::TERM_GT:
    assert(n == 2);
    result = yices_arith_gt_atom(children[0], children[1]);
    break;

  default:
    assert(false);
  }

  return result;
}

type_t yices2_internal::to_yices2_type(expr::term_ref ref) {

  type_t result = NULL_TERM;

  switch (d_tm.term_of(ref).op()) {
  case expr::TYPE_BOOL:
    result = d_bool_type;
    break;
  case expr::TYPE_INTEGER:
    result = d_int_type;
    break;
  case expr::TYPE_REAL:
    result = d_real_type;
    break;
  default:
    assert(false);
  }

  return result;
}

term_t yices2_internal::to_yices2_term(expr::term_ref ref) {

  term_t result = NULL_TERM;

  // Check if in cache already
  term_cache::const_iterator find = d_term_cache.find(ref);
  if (find != d_term_cache.end()) {
    return find->second;
  }

  // The term
  const expr::term& t = d_tm.term_of(ref);

  switch (t.op()) {
  case expr::VARIABLE:
    result = yices_new_uninterpreted_term(to_yices2_type(t[0]));
    yices_set_term_name(result, d_tm.get_variable_name(t).c_str());
    break;
  case expr::CONST_BOOL:
    result = d_tm.get_boolean_constant(t) ? yices_true() : yices_false();
    break;
  case expr::CONST_RATIONAL:
    result = yices_mpq(d_tm.get_rational_constant(t).mpq().get_mpq_t());
    break;
  case expr::TERM_AND:
  case expr::TERM_OR:
  case expr::TERM_NOT:
  case expr::TERM_IMPLIES:
  case expr::TERM_XOR:
  case expr::TERM_ADD:
  case expr::TERM_SUB:
  case expr::TERM_MUL:
  case expr::TERM_DIV:
  case expr::TERM_LEQ:
  case expr::TERM_LT:
  case expr::TERM_GEQ:
  case expr::TERM_GT:
  {
    size_t size = t.size();
    term_t children[size];
    for (size_t i = 0; i < size; ++ i) {
      children[i] = to_yices2_term(t[i]);
    }
    result = mk_yices2_term(t.op(), size, children);
    break;
  }
  default:
    assert(false);
  }

  assert (result != NULL_TERM);
  d_term_cache[ref] = result;

  return result;
}

void yices2_internal::add(expr::term_ref ref) {
  expr::term_ref_strong ref_strong(d_tm, ref);
  d_assertions.push_back(ref_strong);
  term_t yices_term = to_yices2_term(ref);
  yices_assert_formula(d_ctx, yices_term);
}

solver::result yices2_internal::check() {
  smt_status_t status = yices_check_context(d_ctx, 0);
  if (status == STATUS_SAT) {
    model_t *model = yices_get_model(d_ctx, 1);
    yices_print_model(stdout, model);
    yices_free_model(model);
    return solver::SAT;
  } else if (status == STATUS_UNSAT) {
    return solver::UNSAT;
  } else {
    return solver::UNKNOWN;
  }
}

yices2::yices2(expr::term_manager& tm)
: solver(tm)
{
  d_internal = new yices2_internal(tm);
}

yices2::~yices2() {
  delete d_internal;
}

void yices2::add(expr::term_ref f) {
  d_internal->add(f);
}

solver::result yices2::check() {
  return d_internal->check();
}

expr::term_ref yices2::generalize() {
  return expr::term_ref();
}

void yices2::interpolate(std::vector<expr::term_ref>& ) {

}

}
}


