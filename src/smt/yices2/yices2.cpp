/*
 * yices.cpp
 *
 *  Created on: Oct 24, 2014
 *      Author: dejan
 */

#include <gmp.h>
#include <yices.h>
#include <boost/unordered_map.hpp>

#include <iostream>

#include "expr/term.h"
#include "expr/term_manager.h"
#include "expr/rational.h"
#include "smt/yices2/yices2.h"

namespace sal2 {
namespace smt {

/** Yices term hash. */
struct yices_hasher {
  size_t operator()(term_t value) const { return value; }
};

class yices2_internal {

  /** The term manager */
  expr::term_manager& d_tm;

  /** Number of yices instances */
  static int s_instances;

  /** Yices boolean type */
  type_t d_bool_type;

  /** Yices integer type */
  type_t d_int_type;

  /** Yices real type */
  type_t d_real_type;

  /** The yices context */
  context_t *d_ctx;

  /** All assertions we have in context (strong) TODO: push/pop */
  std::vector<expr::term_ref_strong> d_assertions;

  /** The assertions size per push/pop */
  std::vector<size_t> d_assertions_size;

  typedef boost::unordered_map<expr::term_ref, term_t, expr::term_ref_hasher> term_to_yices_cache;
  typedef boost::unordered_map<term_t, expr::term_ref, yices_hasher> yices_to_term_cache;

  /** The map from terms to yices terms */
  term_to_yices_cache d_term_to_yices_cache;

  /** The map from yices terms to SAL terms */
  yices_to_term_cache d_yices_to_term_cache;

  /**
   * Set the term cache from t -> t_yices. If t_yices doesn't exist in the
   * cache already, add the map t_yices -> t.
   */
  void set_term_cache(expr::term_ref t, term_t t_yices) {
    assert(d_term_to_yices_cache.find(t) == d_term_to_yices_cache.end());
    d_term_to_yices_cache[t] = t_yices;
    if (d_yices_to_term_cache.find(t_yices) == d_yices_to_term_cache.end()) {
      d_yices_to_term_cache[t_yices] = t;
    }
  }

  /** Returns the yices term associated with t, or NULL_TERM otherwise */
  term_t get_term_cache(expr::term_ref t) const {
    term_to_yices_cache::const_iterator find = d_term_to_yices_cache.find(t);
    if (find != d_term_to_yices_cache.end()) {
      return find->second;
    } else {
      return NULL_TERM;
    }
  }

  /** Returns our term representative for the yices term t or null otherwise */
  expr::term_ref get_term_cache(term_t t) const {
    yices_to_term_cache::const_iterator find = d_yices_to_term_cache.find(t);
    if (find != d_yices_to_term_cache.end()) {
      return find->second;
    } else {
      return expr::term_ref();
    }
  }

  /** List of variables, for model construction */
  std::vector<expr::term_ref> d_variables;

  /** Last check return */
  smt_status_t d_last_check_status;

public:

  /** Construct an instance of yices with the given temr manager and options */
  yices2_internal(expr::term_manager& tm, const options& opts);

  /** Destroy yices instance */
  ~yices2_internal();

  /** Get the yices version of the term */
  term_t to_yices2_term(expr::term_ref ref);

  /** Get the yices version of the type */
  type_t to_yices2_type(expr::term_ref ref);

  /** Get the sal version of the term */
  expr::term_ref to_term(term_t t);

  /** Make a term given yices operator and children */
  expr::term_ref mk_term(term_constructor_t constructor, const std::vector<expr::term_ref>& children);

  /** Make a yices term with given operator and children */
  term_t mk_yices2_term(expr::term_op op, size_t n, term_t* children);

  /** Add an assertion to yices */
  void add(expr::term_ref ref);

  /** Check satisfiability */
  solver::result check();

  /** Returns the model */
  void get_model(expr::model& m);

  /** Push the context */
  void push();

  /** Pop the context */
  void pop();

  /** Return the generalization */
  expr::term_ref generalize(const std::vector<expr::term_ref>& to_eliminate);
};

int yices2_internal::s_instances = 0;

yices2_internal::yices2_internal(expr::term_manager& tm, const options& opts)
: d_tm(tm)
, d_last_check_status(STATUS_UNKNOWN)
{
  // Initialize
  if (s_instances == 0) {
    yices_init();
  }
  s_instances ++;

  // The basic types
  d_bool_type = yices_bool_type();
  d_int_type = yices_int_type();
  d_real_type = yices_real_type();

  // The context
  d_ctx = yices_new_context(NULL);
  if (d_ctx == 0) {
    throw exception("Yices error (context creation).");
  }
}

yices2_internal::~yices2_internal() {

  // The context
  yices_free_context(d_ctx);

  // Cleanup if the last one
  s_instances--;
  if (s_instances == 0) {
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
    assert(n == 2 || n == 1);
    if (n == 1) {
      result = yices_neg(children[0]);
    } else {
      result = yices_sub(children[0], children[1]);
    }
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
  case expr::TERM_EQ:
    assert(n == 2);
    result = yices_eq(children[0], children[1]);
    break;
  case expr::TERM_ITE:
    assert(n == 3);
    result = yices_ite(children[0], children[1], children[2]);
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

  // Check the term has been translated already
  result = get_term_cache(ref);
  if (result != NULL_TERM) {
    return result;
  }

  // The term
  const expr::term& t = d_tm.term_of(ref);
  expr::term_op t_op = t.op();

  switch (t_op) {
  case expr::VARIABLE:
    result = yices_new_uninterpreted_term(to_yices2_type(t[0]));
    yices_set_term_name(result, d_tm.get_variable_name(t).c_str());
    // Remember, for model construction
    d_variables.push_back(ref);
    break;
  case expr::CONST_BOOL:
    result = d_tm.get_boolean_constant(t) ? yices_true() : yices_false();
    break;
  case expr::CONST_RATIONAL:
    result = yices_mpq(d_tm.get_rational_constant(t).mpq().get_mpq_t());
    break;
  case expr::CONST_INTEGER:
    result = yices_mpz(d_tm.get_integer_constant(t).mpz().get_mpz_t());
    break;
  case expr::TERM_ITE:
  case expr::TERM_EQ:
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

  if (result < 0) {
    throw exception("Yices error (term creation)");
  }

  // Set the cache ref -> result
  set_term_cache(ref, result);

  return result;
}

expr::term_ref yices2_internal::mk_term(term_constructor_t constructor, const std::vector<expr::term_ref>& children) {
  expr::term_ref result;

  switch (constructor) {
  case YICES_ITE_TERM:
    result = d_tm.mk_term(expr::TERM_ITE, children);
    break;
  case YICES_APP_TERM:
    break;
  case YICES_UPDATE_TERM:
    break;
  case YICES_TUPLE_TERM:
    break;
  case YICES_EQ_TERM:
    result = d_tm.mk_term(expr::TERM_EQ, children);
    break;
  case YICES_DISTINCT_TERM:
    break;
  case YICES_FORALL_TERM:
    break;
  case YICES_LAMBDA_TERM:
    break;
  case YICES_NOT_TERM:
    result = d_tm.mk_term(expr::TERM_NOT, children);
    break;
  case YICES_OR_TERM:
    result = d_tm.mk_term(expr::TERM_OR, children);
    break;
  case YICES_XOR_TERM:
    result = d_tm.mk_term(expr::TERM_XOR, children);
    break;
  case YICES_BV_ARRAY:
    break;
  case YICES_BV_DIV:
    break;
  case YICES_BV_REM:
    break;
  case YICES_BV_SDIV:
    break;
  case YICES_BV_SREM:
    break;
  case YICES_BV_SMOD:
    break;
  case YICES_BV_SHL:
    break;
  case YICES_BV_LSHR:
    break;
  case YICES_BV_ASHR:
    break;
  case YICES_BV_GE_ATOM:
    break;
  case YICES_BV_SGE_ATOM:
    break;
  case YICES_ARITH_GE_ATOM:
    break;
  default:
    break;
  }

  return result;
}

expr::term_ref yices2_internal::to_term(term_t t) {

  expr::term_ref result;

  // Check the cache
  result = get_term_cache(t);
  if (!result.is_null()) {
    return result;
  }

  // Get the constructor type of t
  term_constructor_t t_constructor = yices_term_constructor(t);

  switch (t_constructor) {
  // atomic terms
  case YICES_BOOL_CONSTANT: {
    int32_t value;
    yices_bool_const_value(t, &value);
    result = d_tm.mk_boolean_constant(value);
    break;
  }
  case YICES_ARITH_CONSTANT: {
    mpq_t q;
    mpq_init(q);
    yices_rational_const_value(t, q);
    expr::rational r(q);
    result = d_tm.mk_rational_constant(r);
    mpq_clear(q);
  }
  case YICES_BV_CONSTANT: {
    size_t size = yices_term_bitsize(t);
    int32_t* bits = new int32_t[size];
    yices_bv_const_value(t, bits);
    char* bits_str = new char[size + 1];
    bits_str[size] = 0;
    for (size_t i = 0; i < size; ++ i) {
      bits_str[i] = bits[size - i] ? '1' : '0';
    }
    expr::bitvector bv(bits_str);
    result = d_tm.mk_bitvector_constant(bv);
    delete bits_str;
    delete bits;
    break;
  }
  case YICES_SCALAR_CONSTANT:
    // Unsupported
    break;
  case YICES_VARIABLE:
    // Qantifiers, not supported
    break;
  case YICES_UNINTERPRETED_TERM:
    // Variables must be already in the cache
    break;

  // composite terms
  case YICES_ITE_TERM:
  case YICES_APP_TERM:
  case YICES_UPDATE_TERM:
  case YICES_TUPLE_TERM:
  case YICES_EQ_TERM:
  case YICES_DISTINCT_TERM:
  case YICES_FORALL_TERM:
  case YICES_LAMBDA_TERM:
  case YICES_NOT_TERM:
  case YICES_OR_TERM:
  case YICES_XOR_TERM:
  case YICES_BV_ARRAY:
  case YICES_BV_DIV:
  case YICES_BV_REM:
  case YICES_BV_SDIV:
  case YICES_BV_SREM:
  case YICES_BV_SMOD:
  case YICES_BV_SHL:
  case YICES_BV_LSHR:
  case YICES_BV_ASHR:
  case YICES_BV_GE_ATOM:
  case YICES_BV_SGE_ATOM:
  case YICES_ARITH_GE_ATOM: {
    size_t n = yices_term_num_children(t);
    std::vector<expr::term_ref> children;
    for (size_t i = 0; i < n; ++ i) {
      term_t child = yices_term_child(t, i);
      expr::term_ref child_term = to_term(child);
      children.push_back(child_term);
    }
    mk_term(t_constructor, children);
    break;
  }

  // projections
  case YICES_SELECT_TERM:
    break;
  case YICES_BIT_TERM:
    break;

  // sums
  case YICES_BV_SUM:
    break;
  case YICES_ARITH_SUM: {
    mpq_t c_y;
    mpq_init(c_y);
    // sum c_i a_i
    size_t size = yices_term_num_children(t);
    std::vector<expr::term_ref> sum_children;
    for (size_t i = 0; i < size; ++ i) {
      term_t a_y;
      yices_sum_component(t, i, c_y, &a_y);
      expr::term_ref c = d_tm.mk_rational_constant(expr::rational(c_y));
      expr::term_ref a = to_term(a_y);
      sum_children.push_back(d_tm.mk_term(expr::TERM_MUL, c, a));
    }
    result = d_tm.mk_term(expr::TERM_ADD, sum_children);
    mpq_clear(c_y);
    break;
  }

  // products
  case YICES_POWER_PRODUCT:
    break;

  default:
    assert(false);
  }

  // At this point we need to be non-null
  if (result.is_null()) {
    throw exception("Yices error (term creation)");
  }

  // Set the cache ref -> result
  set_term_cache(result, t);

  return result;
}

void yices2_internal::add(expr::term_ref ref) {

  if (output::get_verbosity(std::cout) > 2) {
    std::cout << "yices2: adding " << ref << std::endl;
  }

  // Remember the assertions
  expr::term_ref_strong ref_strong(d_tm, ref);
  d_assertions.push_back(ref_strong);

  // Assert to yices
  term_t yices_term = to_yices2_term(ref);
  int ret = yices_assert_formula(d_ctx, yices_term);
  if (ret < 0) {
    throw exception("Yices error (add).");
  }
}

solver::result yices2_internal::check() {
  d_last_check_status = yices_check_context(d_ctx, 0);
  if (d_last_check_status == STATUS_SAT) {
    return solver::SAT;
  } else if (d_last_check_status == STATUS_UNSAT) {
    return solver::UNSAT;
  } else if (d_last_check_status == STATUS_UNKNOWN) {
    return solver::UNKNOWN;
  } else {
    throw exception("Yices error (check).");
  }
}

void yices2_internal::get_model(expr::model& m) {
  assert(d_last_check_status == STATUS_SAT);

  // Clear any data already there
  m.clear();

  // Get the model from yices
  model_t* yices_model = yices_get_model(d_ctx, true);

  for (size_t i = 0; i < d_variables.size(); ++ i) {
    expr::term_ref var = d_variables[i];
    term_t yices_var = d_term_to_yices_cache[var];
    expr::term_ref var_type = d_tm.type_of(var);

    expr::term_ref var_value;
    switch (d_tm.term_of(var_type).op()) {
    case expr::TYPE_BOOL: {
      int32_t value;
      yices_get_bool_value(yices_model, yices_var, &value);
      var_value = d_tm.mk_boolean_constant(value);
      break;
    }
    case expr::TYPE_INTEGER: {
      // The integer mpz_t value
      mpz_t value;
      mpz_init(value);
      yices_get_mpz_value(yices_model, yices_var, value);
      // The rational mpq_t value
      mpq_t value_q;
      mpq_init(value_q);
      mpq_set_z(value_q, value);
      // Now, the rational
      expr::rational rational_value(value_q);
      var_value = d_tm.mk_rational_constant(rational_value);;
      // Clear the temps
      mpq_clear(value_q);
      mpz_clear(value);
      break;
    }
    case expr::TYPE_REAL: {
      // The integer mpz_t value
      mpq_t value;
      mpq_init(value);
      yices_get_mpq_value(yices_model, yices_var, value);
      // Now, the rational
      expr::rational rational_value(value);
      var_value = d_tm.mk_rational_constant(rational_value);;
      // Clear the temps
      mpq_clear(value);
      break;
    }
    default:
      assert(false);
    }

    // Add the association
    m.set_value(var, var_value);
  }

  // Free the yices model
  yices_free_model(yices_model);
}

void yices2_internal::push() {
  int ret = yices_push(d_ctx);
  if (ret < 0) {
    throw exception("Yices error (push).");
  }
  d_assertions_size.push_back(d_assertions.size());
}

void yices2_internal::pop() {
  int ret = yices_pop(d_ctx);
  if (ret < 0) {
    throw exception("Yices error (pop).");
  }
  size_t size = d_assertions_size.back();
  d_assertions_size.pop_back();
  while (d_assertions.size() > size) {
    d_assertions.pop_back();
  }
}

expr::term_ref yices2_internal::generalize(const std::vector<expr::term_ref>& to_eliminate) {

  if (output::get_verbosity(std::cout) > 2) {
    std::cout << "yices2: generalizing" << std::endl;
  }

  // Get the model
  model_t* m = yices_get_model(d_ctx, true);

  if (output::get_verbosity(std::cout) > 2) {
    std::cout << "model:" << std::endl;
    yices_pp_model(stdout, m, 80, 100, 0);
  }

  // Yices version of the assertions
  term_t* assertions = new term_t[d_assertions.size()];
  for (size_t i = 0; i < d_assertions.size(); ++ i) {
    assertions[i] = to_yices2_term(d_assertions[i]);
  }

  // Yices version of the variables
  term_t* variables = new term_t[to_eliminate.size()];
  for (size_t i = 0; i < to_eliminate.size(); ++ i) {
    variables[i] = to_yices2_term(to_eliminate[i]);
  }

  if (output::get_verbosity(std::cout) > 2) {
    std::cout << "assertions:" << std::endl;
    for (size_t i = 0; i < d_assertions.size(); ++ i) {
      std::cout << i << ": ";
      yices_pp_term(stdout, assertions[i], 80, 100, 0);
    }
    std::cout << "variables:" << std::endl;
    for (size_t i = 0; i < to_eliminate.size(); ++ i) {
      std::cout << i << ": ";
      yices_pp_term(stdout, variables[i], 80, 100, 0);
    }
  }

  // Generalize
  term_t G_y = yices_generalize_model_array(m,
      d_assertions.size(), assertions,
      to_eliminate.size(), variables);
  expr::term_ref G = to_term(G_y);

  if (output::get_verbosity(std::cout) > 2) {
    std::cout << "generalization: " << G << std::endl;
  }

  std::cout << G << std::endl;

  // Free temps
  delete variables;
  delete assertions;
  yices_free_model(m);

  return G;
}

yices2::yices2(expr::term_manager& tm, const options& opts)
: solver("yices2", tm, opts)
{
  d_internal = new yices2_internal(tm, opts);
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

void yices2::get_model(expr::model& m) const {
  d_internal->get_model(m);
}

void yices2::push() {
  d_internal->push();
}

void yices2::pop() {
  d_internal->pop();
}


expr::term_ref yices2::generalize(const std::vector<expr::term_ref>& to_eliminate) {
  return d_internal->generalize(to_eliminate);
}

void yices2::interpolate(std::vector<expr::term_ref>& ) {

}

}
}


