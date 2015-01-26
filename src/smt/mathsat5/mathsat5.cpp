/*
 * mathsat5.cpp
 *
 *  Created on: Oct 24, 2014
 *      Author: dejan
 */

#ifdef WITH_MATHSAT5

#include <gmp.h>
#include <mathsat.h>
#include <boost/unordered_map.hpp>

#include <iostream>

#include "expr/term.h"
#include "expr/term_manager.h"
#include "expr/rational.h"
#include "smt/mathsat5/mathsat5.h"
#include "utils/trace.h"

namespace sal2 {
namespace smt {

/** Yices term hash. */
struct mathsat5_hasher {
  size_t operator()(msat_term value) const { return msat_term_id(value); }
};

/** Equality checks */
struct mathsat5_eq {
  bool operator() (const msat_term& t1, const msat_term& t2) const {
    return msat_term_id(t1) == msat_term_id(t2);
  }
};

class mathsat5_internal {

  /** The term manager */
  expr::term_manager& d_tm;

  /** Number of mathsat5 instances */
  static int s_instances;

  /** All assertions we have in context (strong) TODO: push/pop */
  std::vector<expr::term_ref_strong> d_assertions;

  /** The assertions size per push/pop */
  std::vector<size_t> d_assertions_size;

  typedef boost::unordered_map<expr::term_ref, msat_term, expr::term_ref_hasher> term_to_msat_cache;
  typedef boost::unordered_map<msat_term, expr::term_ref, mathsat5_hasher, mathsat5_eq> msat_to_term_cache;

  /** Bitvector 1 */
  expr::term_ref_strong d_bv1;

  /** Bitvector 0 */
  expr::term_ref_strong d_bv0;

  /** -1 in mathsat */
  msat_term d_msat_minus_one;

  /** Interpolant groups */
  int d_msat_A, d_msat_B;

  /** The map from terms to mathsat terms */
  term_to_msat_cache d_term_to_msat_cache;

  /** The map from mathsat terms to SAL terms */
  msat_to_term_cache d_msat_to_term_cache;

  /**
   * Set the term cache from t -> t_msat. If t_msat doesn't exist in the
   * cache already, add the map t_msat -> t.
   */
  void set_term_cache(expr::term_ref t, msat_term t_msat) {
    assert(d_term_to_msat_cache.find(t) == d_term_to_msat_cache.end());
    d_term_to_msat_cache[t] = t_msat;
    if (d_msat_to_term_cache.find(t_msat) == d_msat_to_term_cache.end()) {
      d_msat_to_term_cache[t_msat] = t;
    }
  }

  /** Returns the mathsat5 term associated with t, or NULL_TERM otherwise */
  msat_term get_term_cache(expr::term_ref t) const {
    term_to_msat_cache::const_iterator find = d_term_to_msat_cache.find(t);
    if (find != d_term_to_msat_cache.end()) {
      return find->second;
    } else {
      msat_term error;
      MSAT_MAKE_ERROR_TERM(error);
      return error;
    }
  }

  /** Returns our term representative for the mathsat5 term t or null otherwise */
  expr::term_ref get_term_cache(msat_term t) const {
    msat_to_term_cache::const_iterator find = d_msat_to_term_cache.find(t);
    if (find != d_msat_to_term_cache.end()) {
      return find->second;
    } else {
      return expr::term_ref();
    }
  }

  /** List of variables, for model construction */
  std::vector<expr::term_ref> d_variables;

  /** Last check return */
  msat_result d_last_check_status;

  /** The instance */
  size_t d_instance;

  /** MathSAT configuration */
  msat_config d_cfg;

  /** The context */
  msat_env d_env;

public:

  /** Construct an instance of mathsat5 with the given temr manager and options */
  mathsat5_internal(expr::term_manager& tm, const options& opts);

  /** Destroy mathsat5 instance */
  ~mathsat5_internal();

  /** Get the mathsat5 version of the term */
  msat_term to_mathsat5_term(expr::term_ref ref);

  /** Get the mathsat5 version of the type */
  msat_type to_mathsat5_type(expr::term_ref ref);

  /** Get the sal version of the term */
  expr::term_ref to_term(msat_term t);

  /** Make a term given mathsat5 operator and children */
  expr::term_ref mk_term(msat_symbol_tag constructor, const std::vector<expr::term_ref>& children);

  /** Make a mathsat5 term with given operator and children */
  msat_term mk_mathsat5_term(expr::term_op op, size_t n, msat_term* children);

  /** Add an assertion to mathsat5 */
  void add(expr::term_ref ref, solver::formula_class f_class);

  /** Check satisfiability */
  solver::result check();

  /** Returns the model */
  void get_model(expr::model& m);

  /** Push the context */
  void push();

  /** Pop the context */
  void pop();

  /** Return the generalization */
  void interpolate(std::vector<expr::term_ref>& projection_out);

  /** Returns the instance id */
  size_t instance() const { return d_instance; }
};

int mathsat5_internal::s_instances = 0;

mathsat5_internal::mathsat5_internal(expr::term_manager& tm, const options& opts)
: d_tm(tm)
, d_last_check_status(MSAT_UNKNOWN)
, d_instance(s_instances)
{
  // Initialize
  s_instances ++;

  // Bitvector bits
  d_bv0 = expr::term_ref_strong(d_tm, d_tm.mk_bitvector_constant(expr::bitvector(1, 0)));
  d_bv1 = expr::term_ref_strong(d_tm, d_tm.mk_bitvector_constant(expr::bitvector(1, 1)));

  // The context
  d_cfg = msat_create_config();
  msat_set_option(d_cfg, "model_generation", "true");
  msat_set_option(d_cfg, "interpolation", "true");
  d_env = msat_create_env(d_cfg);

  // Interpolation groups
  d_msat_A = msat_create_itp_group(d_env);
  d_msat_B = msat_create_itp_group(d_env);

  // Minus one
  d_msat_minus_one = msat_make_number(d_env, "-1");
}

mathsat5_internal::~mathsat5_internal() {
  msat_destroy_env(d_env);
  msat_destroy_config(d_cfg);
  s_instances--;
}

msat_term mathsat5_internal::mk_mathsat5_term(expr::term_op op, size_t n, msat_term* children) {
  msat_term result;
  MSAT_MAKE_ERROR_TERM(result);

  switch (op) {
  case expr::TERM_AND:
    result = children[0];
    for (size_t i = 1; i < n; ++ i) {
      result = msat_make_and(d_env, result, children[i]);
    }
    break;
  case expr::TERM_OR:
    result = children[0];
    for (size_t i = 1; i < n; ++ i) {
      result = msat_make_or(d_env, result, children[i]);
    }
    break;
  case expr::TERM_NOT:
    assert(n == 1);
    result = msat_make_not(d_env, children[0]);
    break;
  case expr::TERM_IMPLIES:
    assert(n == 2);
    result = msat_make_not(d_env, children[0]);
    result = msat_make_or(d_env, result, children[1]);
    break;
  case expr::TERM_XOR:
    assert(n == 2);
    result = msat_make_iff(d_env, children[0], children[1]);
    result = msat_make_not(d_env, result);
    break;
  case expr::TERM_ADD:
    result = children[0];
    for (size_t i = 1; i < n; ++ i) {
      result = msat_make_plus(d_env, result, children[i]);
    }
    break;
  case expr::TERM_SUB:
    if (n == 1) {
      result = msat_make_times(d_env, d_msat_minus_one, children[0]);
    } else {
      assert(n == 2);
      result = msat_make_times(d_env, d_msat_minus_one, children[1]);
      result = msat_make_plus(d_env, children[0], result);
    }
    break;
  case expr::TERM_MUL:
    result = children[0];
    for (size_t i = 1; i < n; ++ i) {
      result = msat_make_times(d_env, result, children[i]);
    }
    break;
  case expr::TERM_DIV: {
    assert(n == 2);
    assert(msat_term_is_number(d_env, children[1]));
    mpq_t constant;
    mpq_init(constant);
    msat_term_to_number(d_env, children[0], constant);
    assert(mpq_sgn(constant));
    mpq_inv(constant, constant);
    char* constant_str = mpq_get_str(0, 10, constant);
    result = msat_make_number(d_env, constant_str);
    mpq_clear(constant);
    result = msat_make_times(d_env, children[0], result);
    break;
  }
  case expr::TERM_LEQ:
    assert(n == 2);
    result = msat_make_leq(d_env, children[0], children[1]);
    break;
  case expr::TERM_LT:
    assert(n == 2);
    result = msat_make_leq(d_env, children[1], children[0]);
    result = msat_make_not(d_env, result);
    break;
  case expr::TERM_GEQ:
    assert(n == 2);
    result = msat_make_leq(d_env, children[1], children[0]);
    break;
  case expr::TERM_GT:
    assert(n == 2);
    result = msat_make_leq(d_env, children[0], children[1]);
    result = msat_make_not(d_env, result);
    break;
  case expr::TERM_EQ:
    assert(n == 2);
    result = msat_make_equal(d_env, children[0], children[1]);
    break;
  case expr::TERM_ITE:
    assert(n == 3);
    result = msat_make_term_ite(d_env, children[0], children[1], children[2]);
    break;
  case expr::TERM_BV_ADD:
    result = children[0];
    for (size_t i = 1; i < n; ++ i) {
      result = msat_make_bv_plus(d_env, result, children[i]);
    }
    break;
  case expr::TERM_BV_SUB:
    assert(n == 2);
    result = msat_make_bv_minus(d_env, children[0], children[1]);
    break;
  case expr::TERM_BV_MUL:
    result = children[0];
    for (size_t i = 1; i < n; ++ i) {
      result = msat_make_bv_times(d_env, result, children[i]);
    }
    break;
  case expr::TERM_BV_UDIV: // NOTE: semantics of division is x/0 = 111...111
    assert(n == 2);
    result = msat_make_bv_udiv(d_env, children[0], children[1]);
    break;
  case expr::TERM_BV_SDIV:
    assert(n == 2);
    result = msat_make_bv_sdiv(d_env, children[0], children[1]);
    break;
  case expr::TERM_BV_UREM:
    assert(n == 2);
    result = msat_make_bv_urem(d_env, children[0], children[1]);
    break;
  case expr::TERM_BV_SREM:
    assert(n == 2);
    result = msat_make_bv_srem(d_env, children[0], children[1]);
    break;
  case expr::TERM_BV_SMOD:
    assert(n == 2);
    MSAT_MAKE_ERROR_TERM(result);
    break;
  case expr::TERM_BV_XOR:
    result = children[0];
    for (size_t i = 1; i < n; ++ i) {
      result = msat_make_bv_xor(d_env, result, children[i]);
    }
    break;
  case expr::TERM_BV_SHL:
    assert(n == 2);
    result = msat_make_bv_lshl(d_env, children[0], children[1]);
    break;
  case expr::TERM_BV_LSHR:
    assert(n == 2);
    result = msat_make_bv_lshr(d_env, children[0], children[1]);
    break;
  case expr::TERM_BV_ASHR:
    assert(n == 2);
    result = msat_make_bv_ashr(d_env, children[0], children[1]);
    break;
  case expr::TERM_BV_NOT:
    assert(n == 1);
    result = msat_make_bv_not(d_env, children[0]);
    break;
  case expr::TERM_BV_AND:
    result = children[0];
    for (size_t i = 1; i < n; ++ i) {
      result = msat_make_bv_and(d_env, result, children[i]);
    }
    break;
  case expr::TERM_BV_OR:
    result = children[0];
    for (size_t i = 1; i < n; ++ i) {
      result = msat_make_bv_or(d_env, result, children[i]);
    }
    break;
  case expr::TERM_BV_NAND:
    assert(n == 2);
    result = msat_make_bv_and(d_env, children[0], children[1]);
    result = msat_make_bv_not(d_env, result);
    break;
  case expr::TERM_BV_NOR:
    assert(n == 2);
    result = msat_make_bv_or(d_env, children[0], children[1]);
    result = msat_make_bv_not(d_env, result);
    break;
  case expr::TERM_BV_XNOR:
    assert(n == 2);
    result = msat_make_bv_xor(d_env, children[0], children[1]);
    result = msat_make_bv_not(d_env, result);
    break;
  case expr::TERM_BV_CONCAT:
    result = children[0];
    for (size_t i = 1; i < n; ++ i) {
      result = msat_make_bv_concat(d_env, result, children[i]);
    }
    break;
  case expr::TERM_BV_ULEQ:
    assert(n == 2);
    result = msat_make_bv_uleq(d_env, children[0], children[1]);
    break;
  case expr::TERM_BV_SLEQ:
    assert(n == 2);
    result = msat_make_bv_sleq(d_env, children[0], children[1]);
    break;
  case expr::TERM_BV_ULT:
    assert(n == 2);
    result = msat_make_bv_ult(d_env, children[0], children[1]);
    break;
  case expr::TERM_BV_SLT:
    assert(n == 2);
    result = msat_make_bv_slt(d_env, children[0], children[1]);
    break;
  case expr::TERM_BV_UGEQ:
    assert(n == 2);
    result = msat_make_bv_uleq(d_env, children[1], children[0]);
    break;
  case expr::TERM_BV_SGEQ:
    assert(n == 2);
    result = msat_make_bv_sleq(d_env, children[1], children[0]);
    break;
  case expr::TERM_BV_UGT:
    assert(n == 2);
    result = msat_make_bv_ult(d_env, children[1], children[0]);
    break;
  case expr::TERM_BV_SGT:
    assert(n == 2);
    result = msat_make_bv_slt(d_env, children[1], children[0]);
    break;
  default:
    assert(false);
  }

  return result;
}

msat_type mathsat5_internal::to_mathsat5_type(expr::term_ref ref) {

  msat_type result;
  MSAT_MAKE_ERROR_TERM(result);

  switch (d_tm.term_of(ref).op()) {
  case expr::TYPE_BOOL:
    result = msat_get_bool_type(d_env);
    break;
  case expr::TYPE_INTEGER:
    result = msat_get_integer_type(d_env);
    break;
  case expr::TYPE_REAL:
    result = msat_get_rational_type(d_env);
    break;
  case expr::TYPE_BITVECTOR: {
    size_t size = d_tm.get_bitvector_type_size(ref);
    result = msat_get_bv_type(d_env, size);
    break;
  }
  default:
    assert(false);
  }

  return result;
}

msat_term mathsat5_internal::to_mathsat5_term(expr::term_ref ref) {

  // Check the term has been translated already
  msat_term result = get_term_cache(ref);
  if (!MSAT_ERROR_TERM(result)) {
    return result;
  }

  // The term
  const expr::term& t = d_tm.term_of(ref);
  expr::term_op t_op = t.op();

  switch (t_op) {
  case expr::VARIABLE: {
    msat_decl var = msat_declare_function(d_env, d_tm.get_variable_name(t).c_str(), to_mathsat5_type(t[0]));
    result = msat_make_constant(d_env, var);
    // Remember, for model construction
    d_variables.push_back(ref);
    break;
  }
  case expr::CONST_BOOL:
    result = d_tm.get_boolean_constant(t) ? msat_make_true(d_env) : msat_make_false(d_env);
    break;
  case expr::CONST_RATIONAL: {
    result = msat_make_number(d_env, d_tm.get_rational_constant(t).mpq().get_str().c_str());
    break;
  }
  case expr::CONST_INTEGER: {
    result = msat_make_number(d_env, d_tm.get_integer_constant(t).mpz().get_str(10).c_str());
    break;
  }
  case expr::CONST_BITVECTOR: {
    expr::bitvector bv = d_tm.get_bitvector_constant(t);
    result = msat_make_bv_number(d_env, bv.mpz().get_str(10).c_str(), bv.size(), 10);
    break;
  }
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
  case expr::TERM_BV_ADD:
  case expr::TERM_BV_SUB:
  case expr::TERM_BV_MUL:
  case expr::TERM_BV_UDIV: // NOTE: semantics of division is x/0 = 111...111
  case expr::TERM_BV_SDIV:
  case expr::TERM_BV_UREM:
  case expr::TERM_BV_SREM:
  case expr::TERM_BV_SMOD:
  case expr::TERM_BV_XOR:
  case expr::TERM_BV_SHL:
  case expr::TERM_BV_LSHR:
  case expr::TERM_BV_ASHR:
  case expr::TERM_BV_NOT:
  case expr::TERM_BV_AND:
  case expr::TERM_BV_OR:
  case expr::TERM_BV_NAND:
  case expr::TERM_BV_NOR:
  case expr::TERM_BV_XNOR:
  case expr::TERM_BV_CONCAT:
  case expr::TERM_BV_ULEQ:
  case expr::TERM_BV_SLEQ:
  case expr::TERM_BV_ULT:
  case expr::TERM_BV_SLT:
  case expr::TERM_BV_UGEQ:
  case expr::TERM_BV_SGEQ:
  case expr::TERM_BV_UGT:
  case expr::TERM_BV_SGT:
  {
    size_t size = t.size();
    msat_term children[size];
    for (size_t i = 0; i < size; ++ i) {
      children[i] = to_mathsat5_term(t[i]);
    }
    result = mk_mathsat5_term(t.op(), size, children);
    break;
  }
  case expr::TERM_BV_EXTRACT: {
    const expr::bitvector_extract& extract = d_tm.get_bitvector_extract(t);
    msat_term child = to_mathsat5_term(t[0]);
    result = msat_make_bv_extract(d_env, extract.high, extract.low, child);
    break;
  }
  default:
    assert(false);
  }

  if (MSAT_ERROR_TERM(result)) {
    throw exception("Mathsat error (term creation)");
  }

  // Set the cache ref -> result
  set_term_cache(ref, result);

  return result;
}

expr::term_ref mathsat5_internal::to_term(msat_term t) {

  expr::term_ref result;

  // Check the cache
  result = get_term_cache(t);
  if (!result.is_null()) {
    return result;
  }

  size_t out_msb, out_lsb, out_amount;

  if (msat_term_is_true(d_env, t)) {
  } else if (msat_term_is_false(d_env, t)) {
  } else if (msat_term_is_boolean_constant(d_env, t)) {
  } else if (msat_term_is_atom(d_env, t)) {
  } else if (msat_term_is_number(d_env, t)) {
  } else if (msat_term_is_and(d_env, t)) {
  } else if (msat_term_is_or(d_env, t)) {
  } else if (msat_term_is_not(d_env, t)) {
  } else if (msat_term_is_iff(d_env, t)) {
  } else if (msat_term_is_term_ite(d_env, t)) {
  } else if (msat_term_is_constant(d_env, t)) {
  } else if (msat_term_is_equal(d_env, t)) {
  } else if (msat_term_is_leq(d_env, t)) {
  } else if (msat_term_is_plus(d_env, t)) {
  } else if (msat_term_is_times(d_env, t)) {
  } else if (msat_term_is_bv_concat(d_env, t)) {
  } else if (msat_term_is_bv_extract(d_env, t, &out_msb, &out_lsb)) {
  } else if (msat_term_is_bv_or(d_env, t)) {
  } else if (msat_term_is_bv_xor(d_env, t)) {
  } else if (msat_term_is_bv_and(d_env, t)) {
  } else if (msat_term_is_bv_not(d_env, t)) {
  } else if (msat_term_is_bv_plus(d_env, t)) {
  } else if (msat_term_is_bv_minus(d_env, t)) {
  } else if (msat_term_is_bv_times(d_env, t)) {
  } else if (msat_term_is_bv_neg(d_env, t)) {
  } else if (msat_term_is_bv_udiv(d_env, t)) {
  } else if (msat_term_is_bv_urem(d_env, t)) {
  } else if (msat_term_is_bv_sdiv(d_env, t)) {
  } else if (msat_term_is_bv_srem(d_env, t)) {
  } else if (msat_term_is_bv_ult(d_env, t)) {
  } else if (msat_term_is_bv_uleq(d_env, t)) {
  } else if (msat_term_is_bv_slt(d_env, t)) {
  } else if (msat_term_is_bv_sleq(d_env, t)) {
  } else if (msat_term_is_bv_lshl(d_env, t)) {
  } else if (msat_term_is_bv_lshr(d_env, t)) {
  } else if (msat_term_is_bv_ashr(d_env, t)) {
  } else if (msat_term_is_bv_zext(d_env, t, &out_amount)) {
  } else if (msat_term_is_bv_sext(d_env, t, &out_amount)) {
  } else if (msat_term_is_bv_rol(d_env, t, &out_amount)) {
  } else if (msat_term_is_bv_ror(d_env, t, &out_amount)) {
  } else if (msat_term_is_bv_comp(d_env, t)) {
  }

  // At this point we need to be non-null
  if (result.is_null()) {
    throw exception("Yices error (term creation)");
  }

  // Set the cache ref -> result
  set_term_cache(result, t);

  return result;
}

void mathsat5_internal::add(expr::term_ref ref, solver::formula_class f_class) {
  // Remember the assertions
  expr::term_ref_strong ref_strong(d_tm, ref);
  d_assertions.push_back(ref_strong);

  // Set the interpolation group
  if (f_class == solver::CLASS_C) {
    msat_set_itp_group(d_env, d_msat_B);
  } else {
    msat_set_itp_group(d_env, d_msat_A);
  }

  // Assert to mathsat5
  msat_term m_term = to_mathsat5_term(ref);
  int ret = msat_assert_formula(d_env, m_term);
  if (ret != 0) {
    throw exception("MathSAT5 error (add).");
  }
}

solver::result mathsat5_internal::check() {
  d_last_check_status = msat_solve(d_env);

  switch (d_last_check_status) {
  case MSAT_UNKNOWN:
    return solver::UNKNOWN;
  case MSAT_UNSAT:
    return solver::UNSAT;
  case MSAT_SAT:
    return solver::SAT;
  default:
    throw exception("MathSAT error (check).");
  }

  return solver::UNKNOWN;
}

void mathsat5_internal::get_model(expr::model& m) {

  assert(d_last_check_status == MSAT_SAT);

  // Clear any data already there
  m.clear();

  // Get the model from mathsat
  for (size_t i = 0; i < d_variables.size(); ++ i) {
    expr::term_ref var = d_variables[i];
    expr::term_ref var_type = d_tm.type_of(var);
    expr::term_ref var_value;

    msat_term m_var = d_term_to_msat_cache[var];
    msat_term m_value = msat_get_model_value(d_env, m_var);
    assert(!MSAT_ERROR_TERM(m_value));

    switch (d_tm.term_of(var_type).op()) {
    case expr::TYPE_BOOL: {
      assert(msat_term_is_boolean_constant(d_env, m_value));
      var_value = d_tm.mk_boolean_constant(msat_term_is_true(d_env, m_value));
      break;
    }
    case expr::TYPE_INTEGER: {
      assert(msat_term_is_number(d_env, m_value));
      mpq_t value_q;
      mpq_init(value_q);
      msat_term_to_number(d_env, m_value, value_q);
      // The rational
      expr::rational rational_value(value_q);
      assert(rational_value.is_integer());
      var_value = d_tm.mk_integer_constant(rational_value.get_numerator());
      // Clear the temps
      mpq_clear(value_q);
      break;
    }
    case expr::TYPE_REAL: {
      assert(msat_term_is_number(d_env, m_value));
      mpq_t value;
      mpq_init(value);
      msat_term_to_number(d_env, m_value, value);
      expr::rational rational_value(value);
      var_value = d_tm.mk_rational_constant(rational_value);
      mpq_clear(value);
      break;
    }
    case expr::TYPE_BITVECTOR: {
      assert(msat_term_is_number(d_env, m_value));
      mpq_t value_q;
      mpq_init(value_q);
      msat_term_to_number(d_env, m_value, value_q);
      // The rational
      expr::rational rational_value(value_q);
      assert(rational_value.is_integer());
      expr::bitvector bv_value(d_tm.get_bitvector_type_size(var_type), rational_value.get_numerator());
      var_value = d_tm.mk_bitvector_constant(bv_value);
      // Clear the temps
      mpq_clear(value_q);
      break;
    }
    default:
      assert(false);
    }

    // Add the association
    m.set_value(var, var_value);
  }
}

void mathsat5_internal::interpolate(std::vector<expr::term_ref>& projection_out) {
  int ga[1] = { d_msat_A };
  msat_term I = msat_get_interpolant(d_env, ga, 1);
  projection_out.push_back(to_term(I));
}

void mathsat5_internal::push() {
  int ret = msat_push_backtrack_point(d_env);
  if (ret) {
    throw exception("MathSAT error (push).");
  }
  d_assertions_size.push_back(d_assertions.size());
}

void mathsat5_internal::pop() {
  int ret = msat_pop_backtrack_point(d_env);
  if (ret) {
    throw exception("MathSAT error (pop).");
  }
  size_t size = d_assertions_size.back();
  d_assertions_size.pop_back();
  while (d_assertions.size() > size) {
    d_assertions.pop_back();
  }
}

mathsat5::mathsat5(expr::term_manager& tm, const options& opts)
: solver("mathsat5", tm, opts)
{
  d_internal = new mathsat5_internal(tm, opts);
}

mathsat5::~mathsat5() {
  delete d_internal;
}

void mathsat5::add(expr::term_ref f, formula_class f_class) {
  TRACE("mathsat5") << "mathsat5[" << d_internal->instance() << "]: adding " << f << std::endl;
  d_internal->add(f, f_class);
}

solver::result mathsat5::check() {
  TRACE("mathsat5") << "mathsat5[" << d_internal->instance() << "]: check()" << std::endl;
  return d_internal->check();
}

void mathsat5::get_model(expr::model& m) const {
  TRACE("mathsat5") << "mathsat5[" << d_internal->instance() << "]: get_model()" << std::endl;
  d_internal->get_model(m);
}

void mathsat5::push() {
  TRACE("mathsat5") << "mathsat5[" << d_internal->instance() << "]: push()" << std::endl;
  d_internal->push();
}

void mathsat5::pop() {
  TRACE("mathsat5") << "mathsat5[" << d_internal->instance() << "]: pop()" << std::endl;
  d_internal->pop();
}


void mathsat5::interpolate(std::vector<expr::term_ref>& interpolation_out) {
  TRACE("mathsat5") << "mathsat5[" << d_internal->instance() << "]: interpolating" << std::endl;
  d_internal->interpolate(interpolation_out);
}

}
}

#endif
