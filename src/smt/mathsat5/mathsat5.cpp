/*
 * yices.cpp
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
  typedef boost::unordered_map<msat_term, expr::term_ref, mathsat5_hasher> msat_to_term_cache;

  /** Bitvector 1 */
  expr::term_ref_strong d_bv1;

  /** Bitvector 0 */
  expr::term_ref_strong d_bv0;


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

  /** Returns the yices term associated with t, or NULL_TERM otherwise */
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

  /** Returns our term representative for the yices term t or null otherwise */
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

  /** Construct an instance of yices with the given temr manager and options */
  mathsat5_internal(expr::term_manager& tm, const options& opts);

  /** Destroy yices instance */
  ~mathsat5_internal();

  /** Get the yices version of the term */
  msat_term to_mathsat5_term(expr::term_ref ref);

  /** Get the yices version of the type */
  msat_type to_mathsat5_type(expr::term_ref ref);

  /** Get the sal version of the term */
  expr::term_ref to_term(msat_term t);

  /** Make a term given yices operator and children */
  expr::term_ref mk_term(msat_symbol_tag constructor, const std::vector<expr::term_ref>& children);

  /** Make a yices term with given operator and children */
  msat_term mk_mathsat5_term(expr::term_op op, size_t n, msat_term* children);

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
  void generalize(const std::vector<expr::term_ref>& to_eliminate, std::vector<expr::term_ref>& projection_out);

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
  d_env = msat_create_env(d_cfg);
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
    MSAT_MAKE_ERROR_TERM(result);
    break;
  case expr::TERM_XOR:
    MSAT_MAKE_ERROR_TERM(result);
    break;
  case expr::TERM_ADD:
    result = children[0];
    for (size_t i = 1; i < n; ++ i) {
      result = msat_make_plus(d_env, result, children[i]);
    }
    break;
  case expr::TERM_SUB:
    MSAT_MAKE_ERROR_TERM(result);
    break;
  case expr::TERM_MUL:
    result = children[0];
    for (size_t i = 1; i < n; ++ i) {
      result = msat_make_times(d_env, result, children[i]);
    }
    break;
  case expr::TERM_DIV:
    MSAT_MAKE_ERROR_TERM(result);
    break;
  case expr::TERM_LEQ:
    assert(n == 2);
    result = msat_make_leq(d_env, children[0], children[1]);
    break;
  case expr::TERM_LT:
    assert(n == 2);
    MSAT_MAKE_ERROR_TERM(result);
    break;
  case expr::TERM_GEQ:
    assert(n == 2);
    MSAT_MAKE_ERROR_TERM(result);
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
    result = msat_make_bv_ult(d_env, children[0], children[1]);
    result = msat_make_not(d_env, result);
    break;
  case expr::TERM_BV_SGEQ:
    assert(n == 2);
    result = msat_make_bv_slt(d_env, children[0], children[1]);
    result = msat_make_not(d_env, result);
    break;
  case expr::TERM_BV_UGT:
    assert(n == 2);
    result = msat_make_bv_uleq(d_env, children[0], children[1]);
    result = msat_make_not(d_env, result);
    break;
  case expr::TERM_BV_SGT:
    assert(n == 2);
    result = msat_make_bv_sleq(d_env, children[0], children[1]);
    result = msat_make_not(d_env, result);
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
    result = msat_make_bv_number();
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
    term_t children[size];
    for (size_t i = 0; i < size; ++ i) {
      children[i] = to_mathsat5_term(t[i]);
    }
    result = mk_mathsat5_term(t.op(), size, children);
    break;
  }
  case expr::TERM_BV_EXTRACT: {
    const expr::bitvector_extract& extract = d_tm.get_bitvector_extract(t);
    term_t child = to_mathsat5_term(t[0]);
    result = yices_bvextract(child, extract.low, extract.high);
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

expr::term_ref mathsat5_internal::mk_term(term_constructor_t constructor, const std::vector<expr::term_ref>& children) {
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
    result = d_tm.mk_term(expr::TERM_BV_UGEQ, children);
    break;
  case YICES_BV_SGE_ATOM:
    result = d_tm.mk_term(expr::TERM_BV_SGEQ, children);
    break;
  case YICES_ARITH_GE_ATOM:
    result = d_tm.mk_term(expr::TERM_GEQ, children);
    break;
  default:
    break;
  }

  return result;
}

static
expr::bitvector yices_bv_to_bitvector(size_t size, int32_t* bits) {
  char* bits_str = new char[size + 1];
  bits_str[size] = 0;
  for (size_t i = 0; i < size; ++ i) {
    bits_str[i] = bits[size-i-1] ? '1' : '0';
  }
  expr::bitvector bv(bits_str);
  delete bits_str;
  return bv;
}

expr::term_ref mathsat5_internal::to_term(term_t t) {

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
    break;
  }
  case YICES_BV_CONSTANT: {
    size_t size = yices_term_bitsize(t);
    int32_t* bits = new int32_t[size];
    yices_bv_const_value(t, bits);
    result = d_tm.mk_bitvector_constant(yices_bv_to_bitvector(size, bits));
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
    result = mk_term(t_constructor, children);
    break;
  }

  // projections
  case YICES_SELECT_TERM:
    break;
  case YICES_BIT_TERM: {
    // Selects a bit, and the result is Boolean
    size_t index = yices_proj_index(t);
    expr::term_ref argument = to_term(yices_proj_arg(t));
    result = d_tm.mk_bitvector_extract(argument, expr::bitvector_extract(index, index));
    // Convert to boolean
    result = d_tm.mk_term(expr::TERM_EQ, result, d_bv1);
    break;
  }
  // sums
  case YICES_BV_SUM: {
    // sum a_i * t_i
    size_t bv_size = yices_term_bitsize(t);
    int32_t* a_i_bits = new int32_t[bv_size];
    size_t size = yices_term_num_children(t);
    std::vector<expr::term_ref> sum_children;
    for (size_t i = 0; i < size; ++i) {
      term_t t_i_yices;
      yices_bvsum_component(t, i, a_i_bits, &t_i_yices);
      expr::term_ref a_i = d_tm.mk_bitvector_constant(yices_bv_to_bitvector(bv_size, a_i_bits));
      if (t_i_yices != NULL_TERM) {
        expr::term_ref t_i = to_term(t_i_yices);
        sum_children.push_back(d_tm.mk_term(expr::TERM_BV_MUL, a_i, t_i));
      } else {
        sum_children.push_back(a_i);
      }
    }
    if (size == 1) {
      result = sum_children[0];
    } else {
      result = d_tm.mk_term(expr::TERM_BV_ADD, sum_children);
    }
    delete a_i_bits;
    break;
  }
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
      if (a_y != NULL_TERM) {
        expr::term_ref a = to_term(a_y);
        sum_children.push_back(d_tm.mk_term(expr::TERM_MUL, c, a));
      } else {
        sum_children.push_back(c);
      }
    }
    if (size == 1) {
      result = sum_children[0];
    } else {
      result = d_tm.mk_term(expr::TERM_ADD, sum_children);
    }
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

void mathsat5_internal::add(expr::term_ref ref) {
  // Remember the assertions
  expr::term_ref_strong ref_strong(d_tm, ref);
  d_assertions.push_back(ref_strong);

  // Assert to yices
  term_t yices_term = to_mathsat5_term(ref);
  int ret = yices_assert_formula(d_ctx, yices_term);
  if (ret < 0) {
    throw exception("Yices error (add).");
  }
}

solver::result mathsat5_internal::check() {
  d_last_check_status = yices_check_context(d_ctx, 0);

  switch (d_last_check_status) {
  case STATUS_SAT:
    return solver::SAT;
  case STATUS_UNSAT:
    return solver::UNSAT;
  case STATUS_UNKNOWN:
    return solver::UNKNOWN;
  default:
    throw exception("Yices error (check).");
  }

  return solver::UNKNOWN;
}

static
expr::bitvector bitvector_from_int32(size_t size, int32_t* value) {
  char* value_str = new char[size+1];
  for (size_t i = 0; i < size; ++ i) {
    value_str[size - i - 1] = value[i] ? '1' : '0';
  }
  value_str[size] = 0;
  expr::bitvector bv(value_str);
  delete value_str;
  return bv;
}

void mathsat5_internal::get_model(expr::model& m) {
  assert(d_last_check_status == STATUS_SAT);

  // Clear any data already there
  m.clear();

  // Get the model from yices
  model_t* yices_model = yices_get_model(d_ctx, true);

  for (size_t i = 0; i < d_variables.size(); ++ i) {
    expr::term_ref var = d_variables[i];
    term_t yices_var = d_term_to_msat_cache[var];
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
    case expr::TYPE_BITVECTOR: {
      size_t size = d_tm.get_bitvector_type_size(var_type);
      int32_t* value = new int32_t[size];
      yices_get_bv_value(yices_model, yices_var, value);
      expr::bitvector bv = bitvector_from_int32(size, value);
      var_value = d_tm.mk_bitvector_constant(bv);
      delete value;
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

void mathsat5_internal::push() {
  int ret = yices_push(d_ctx);
  if (ret < 0) {
    throw exception("Yices error (push).");
  }
  d_assertions_size.push_back(d_assertions.size());
}

void mathsat5_internal::pop() {
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

void mathsat5_internal::generalize(const std::vector<expr::term_ref>& to_eliminate, std::vector<expr::term_ref>& projection_out) {

  // Get the model
  model_t* m = yices_get_model(d_ctx, true);

  if (output::get_verbosity(std::cout) > 2) {
    std::cout << "model:" << std::endl;
    yices_pp_model(stdout, m, 80, 100, 0);
  }

  // Yices version of the assertions
  term_t* assertions = new term_t[d_assertions.size()];
  for (size_t i = 0; i < d_assertions.size(); ++ i) {
    assertions[i] = to_mathsat5_term(d_assertions[i]);
  }

  // Yices version of the variables
  term_t* variables = new term_t[to_eliminate.size()];
  for (size_t i = 0; i < to_eliminate.size(); ++ i) {
    variables[i] = to_mathsat5_term(to_eliminate[i]);
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
  term_vector_t G_y;
  yices_init_term_vector(&G_y);
  int32_t ret = yices_generalize_model_array(m, d_assertions.size(), assertions, to_eliminate.size(), variables, YICES_GEN_DEFAULT, &G_y);
  if (ret < 0) {
    throw exception("Generalization failed in Yices.");
  }
  for (size_t i = 0; i < G_y.size; ++ i) {
    projection_out.push_back(to_term(G_y.data[i]));
  }
  yices_delete_term_vector(&G_y);

  if (output::get_verbosity(std::cout) > 2) {
    std::cout << "generalization: " << std::endl;
    for (size_t i = 0; i < projection_out.size(); ++ i) {
      std::cout << i << ": " << projection_out[i] << std::endl;
    }
  }

  // Free temps
  delete variables;
  delete assertions;
  yices_free_model(m);
}

mathsat5::mathsat5(expr::term_manager& tm, const options& opts)
: solver("mathsat5", tm, opts)
{
  d_internal = new mathsat5_internal(tm, opts);
}

mathsat5::~mathsat5() {
  delete d_internal;
}

void mathsat5::add(expr::term_ref f) {
  TRACE("mathsat5") << "mathsat5[" << d_internal->instance() << "]: adding " << f << std::endl;
  d_internal->add(f);
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


void mathsat5::generalize(const std::vector<expr::term_ref>& to_eliminate, std::vector<expr::term_ref>& projection_out) {
  TRACE("mathsat5") << "mathsat5[" << d_internal->instance() << "]: generalizing" << std::endl;
  d_internal->generalize(to_eliminate, projection_out);
}

void mathsat5::interpolate(std::vector<expr::term_ref>& ) {

}

}
}

#endif
