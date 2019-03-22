/**
 * This file is part of sally.
 * Copyright (C) 2015 SRI International.
 *
 * Sally is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Sally is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with sally.  If not, see <http://www.gnu.org/licenses/>.
 */

#ifdef WITH_MATHSAT5

#include <gmp.h>
#include <mathsat.h>
#include <msatexistelim.h>
#include <boost/unordered_map.hpp>

#include <iostream>
#include <fstream>
#include <iomanip>

#include "expr/term.h"
#include "expr/term_manager.h"
#include "expr/gc_relocator.h"

#include "expr/rational.h"
#include "smt/mathsat5/mathsat5.h"
#include "smt/mathsat5/mathsat5_term_cache.h"
#include "utils/trace.h"

#define unused_var(x) { (void)x; }

namespace sally {
namespace smt {

std::ostream& operator << (std::ostream& out, const msat_term& t) {
  char* t_str = msat_term_repr(t);
  out << t_str;
  msat_free(t_str);
  return out;
}

class mathsat5_internal {

  /** The term manager */
  expr::term_manager& d_tm;

  /** Options */
  const options& d_opts;

  /** Number of mathsat5 instances */
  static int s_instances;

  /** All assertions we have in context (strong) */
  std::vector<expr::term_ref_strong> d_assertions;

  /** Mathsat assertions, for debug purposes */
  std::vector<msat_term> d_assertions_mathsat;

  /** Classes of the assertions */
  std::vector<smt::solver::formula_class> d_assertion_classes;

  typedef expr::hash_map_to_term_ref<msat_term, mathsat5_hasher, mathsat5_eq> msat_to_term_cache;

  /** Map from mathsat assertions to our assertions */
  msat_to_term_cache d_assertion_map;

  /** The assertions size per push/pop */
  std::vector<size_t> d_assertions_size;

  /** Bitvector 1 */
  expr::term_ref_strong d_bv1;

  /** Bitvector 0 */
  expr::term_ref_strong d_bv0;

  /** List of variables, for model construction */
  std::vector<expr::term_ref> d_variables;

  /** Last check return */
  msat_result d_last_check_status;

  /** The instance */
  size_t d_instance;

  /** Cache */
  mathsat5_term_cache* d_term_cache;

  /** MathSAT configuration */
  msat_config d_cfg;

  /** The context */
  msat_env d_env;

  /** ITP group A */
  int d_itp_A;

  /** ITP group B */
  int d_itp_B;

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

  /** Check the model when sat */
  void check_model();

  /** Returns the model */
  expr::model::ref get_model();

  /** Push the context */
  void push();

  /** Pop the context */
  void pop();

  /** Return the generalization */
  void generalize(solver::generalization_type type, const std::set<expr::term_ref>& vars_to_keep, const std::set<expr::term_ref>& vars_to_elim, std::vector<expr::term_ref>& out);

  /** Return the interpolation */
  void interpolate(std::vector<expr::term_ref>& out);

  /** Return the unsat core */
  void get_unsat_core(std::vector<expr::term_ref>& out);

  /** Returns the instance id */
  size_t instance() const { return d_instance; }

  /** Stuff we support */
  bool supports(solver::feature f) const {
    switch (f) {
    case solver::INTERPOLATION:
      return true;
    case solver::UNSAT_CORE:
      return d_opts.get_bool("mathsat5-unsat-cores");
    case solver::GENERALIZATION:
      return d_opts.get_bool("mathsat5-generalize-trivial") || d_opts.get_bool("mathsat5-generalize-qe");
    default:
      return false;
    }
  }

  /* Collect terms */
  void gc_collect(const expr::gc_relocator& gc_reloc);

  /** Collect garbage */
  void gc();

};

int mathsat5_internal::s_instances = 0;

mathsat5_internal::mathsat5_internal(expr::term_manager& tm, const options& opts)
: d_tm(tm)
, d_opts(opts)
, d_last_check_status(MSAT_UNKNOWN)
, d_instance(s_instances)
, d_term_cache(mathsat5_term_cache::get_cache(tm))
, d_itp_A(0)
, d_itp_B(0)
{

  s_instances ++;

  // Bitvector bits
  d_bv0 = expr::term_ref_strong(d_tm, d_tm.mk_bitvector_constant(expr::bitvector(1, 0)));
  d_bv1 = expr::term_ref_strong(d_tm, d_tm.mk_bitvector_constant(expr::bitvector(1, 1)));

  // The context
  if (opts.has_option("solver-logic")) {
    std::string logic = opts.get_string("solver-logic");
    d_cfg = msat_create_default_config(logic.c_str());
  } else {
    d_cfg = msat_create_config();
  }

  msat_set_option(d_cfg, "model_generation", "true");
  msat_set_option(d_cfg, "interpolation", "true");
  // msat_set_option(d_cfg, "dpll.interpolation_mode", "2");
  // msat_set_option(d_cfg, "dpll.proof_simplification", "true");
  // msat_set_option(d_cfg, "theory.la.interpolation_mode", "0");
  msat_set_option(d_cfg, "theory.la.split_rat_eq", "false");
  msat_set_option(d_cfg, "theory.bv.eager", "false");
  msat_set_option(d_cfg, "theory.bv.div_by_zero_mode", "0");
  msat_set_option(d_cfg, "theory.euf.enabled", "false");
  msat_set_option(d_cfg, "preprocessor.simplification", "0");

  if (opts.get_bool("mathsat5-unsat-cores")) {
    msat_set_option(d_cfg, "unsat_core_generation", "1");
  }

  if (opts.get_bool("mathsat5-generate-api-log")) {
   msat_set_option(d_cfg, "debug.api_call_trace", "2");
   msat_set_option(d_cfg, "debug.api_call_trace_dump_config", "true");
   std::stringstream ss;
   ss << "mathsat_" << s_instances << ".c";
   msat_set_option(d_cfg, "debug.api_call_trace_filename", ss.str().c_str());
  }

  if (MSAT_ERROR_CONFIG(d_cfg)) {
    throw exception("Error in Mathsat5 initialization");
  }

  // Create an environment sharing terms with the master
  d_env = msat_create_shared_env(d_cfg, d_term_cache->get_msat_env());
  if (MSAT_ERROR_ENV(d_env)) {
    throw exception("Error in MathSAT5 initialization");
  }

  d_itp_A = msat_create_itp_group(d_env);
  d_itp_B = msat_create_itp_group(d_env);
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
  case expr::TERM_SUB: {
    msat_term msat_minus_one = msat_make_number(d_env, "-1");
    if (n == 1) {
      result = msat_make_times(d_env, msat_minus_one, children[0]);
    } else {
      assert(n == 2);
      result = msat_make_times(d_env, msat_minus_one, children[1]);
      result = msat_make_plus(d_env, children[0], result);
    }
    break;
  }
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
    msat_term_to_number(d_env, children[1], constant);
    assert(mpq_sgn(constant));
    mpq_inv(constant, constant);
    char* constant_str = mpq_get_str(0, 10, constant);
    result = msat_make_number(d_env, constant_str);
    mpq_clear(constant);
    free(constant_str);
    result = msat_make_times(d_env, children[0], result);
    break;
  }
  case expr::TERM_LEQ:
    assert(n == 2);
    result = msat_make_leq(d_env, children[0], children[1]);
    break;
  case expr::TERM_LT:
    assert(n == 2);
    // x < y = y > x = not (y <= x)
    result = msat_make_leq(d_env, children[1], children[0]);
    result = msat_make_not(d_env, result);
    break;
  case expr::TERM_GEQ:
    assert(n == 2);
    // x >= y = y <= x
    result = msat_make_leq(d_env, children[1], children[0]);
    break;
  case expr::TERM_GT:
    assert(n == 2);
    // x > y = not (x <= y)
    result = msat_make_leq(d_env, children[0], children[1]);
    result = msat_make_not(d_env, result);
    break;
  case expr::TERM_EQ: {
    assert(n == 2);
    if (msat_is_bool_type(d_env, msat_term_get_type(children[0]))) {
      result = msat_make_iff(d_env, children[0], children[1]);
    } else {
      result = msat_make_equal(d_env, children[0], children[1]);
    }
    break;
  }
  case expr::TERM_ITE:
    assert(n == 3);
    if (msat_is_bool_type(d_env, msat_term_get_type(children[1]))) {
      // ITE(c, t, f) = c*t + (!c)*f
      msat_term true_branch = msat_make_and(d_env, children[0], children[1]);
      msat_term false_branch = msat_make_and(d_env, msat_make_not(d_env, children[0]), children[2]);
      result = msat_make_or(d_env, true_branch, false_branch);
    } else {
      result = msat_make_term_ite(d_env, children[0], children[1], children[2]);
    }
    break;
  case expr::TERM_BV_ADD:
    result = children[0];
    for (size_t i = 1; i < n; ++ i) {
      result = msat_make_bv_plus(d_env, result, children[i]);
    }
    break;
  case expr::TERM_BV_SUB:
    if (n == 1) {
      result = msat_make_bv_neg(d_env, children[0]);
    } else {
      assert(n == 2);
      result = msat_make_bv_minus(d_env, children[0], children[1]);
    }
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
  msat_term result = d_term_cache->get_term_cache(ref);
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
    assert(size > 0);
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
    throw exception("Mathsat error (unsupported term type): ") << t_op;
  }

  if (MSAT_ERROR_TERM(result)) {
    throw exception("Mathsat error (term creation)");
  }

  // Set the cache ref -> result
  d_term_cache->set_term_cache(ref, result);

  return result;
}

expr::term_ref mathsat5_internal::to_term(msat_term t) {

  expr::term_ref result;

  // Check the cache
  result = d_term_cache->get_term_cache(t);
  if (!result.is_null()) {
    return result;
  }

  size_t out_msb, out_lsb, out_amount;

  if (msat_term_is_true(d_env, t)) {
    result = d_tm.mk_boolean_constant(true);
  } else if (msat_term_is_false(d_env, t)) {
    result = d_tm.mk_boolean_constant(false);
  } else if (msat_term_is_number(d_env, t)) {
    mpq_t number;
    mpq_init(number);
    msat_term_to_number(d_env, t, number);
    expr::rational rational(number);

    if (rational.is_integer()) {
      msat_type t_type = msat_term_get_type(t);
      size_t bv_size;
      if (msat_is_bv_type(d_env, t_type, &bv_size)) {
        result = d_tm.mk_bitvector_constant(expr::bitvector(bv_size, rational.get_numerator()));
      } else {
        result = d_tm.mk_rational_constant(rational);
      }
    } else {
      result = d_tm.mk_rational_constant(rational);
    }
    mpq_clear(number);

  } else if (msat_term_is_and(d_env, t)) {
    size_t size = msat_term_arity(t);
    std::vector<expr::term_ref> children;
    for(size_t i = 0; i < size; ++ i) {
      msat_term child = msat_term_get_arg(t, i);
      children.push_back(to_term(child));
    }
    result = d_tm.mk_and(children);
  } else if (msat_term_is_or(d_env, t)) {
    size_t size = msat_term_arity(t);
    std::vector<expr::term_ref> children;
    for(size_t i = 0; i < size; ++ i) {
      msat_term child = msat_term_get_arg(t, i);
      children.push_back(to_term(child));
    }
    result = d_tm.mk_or(children);
  } else if (msat_term_is_not(d_env, t)) {
    msat_term child = msat_term_get_arg(t, 0);
    result = d_tm.mk_term(expr::TERM_NOT, to_term(child));
  } else if (msat_term_is_iff(d_env, t)) {
    msat_term child1 = msat_term_get_arg(t, 0);
    msat_term child2 = msat_term_get_arg(t, 1);
    result = d_tm.mk_term(expr::TERM_EQ, to_term(child1), to_term(child2));
  } else if (msat_term_is_term_ite(d_env, t)) {
    msat_term child1 = msat_term_get_arg(t, 0);
    msat_term child2 = msat_term_get_arg(t, 1);
    msat_term child3 = msat_term_get_arg(t, 2);
    result = d_tm.mk_term(expr::TERM_ITE, to_term(child1), to_term(child2), to_term(child3));
  } else if (msat_term_is_constant(d_env, t)) {
    // Should have been cached, no new variables allowed
    assert(false);
  } else if (msat_term_is_equal(d_env, t)) {
    msat_term child1 = msat_term_get_arg(t, 0);
    msat_term child2 = msat_term_get_arg(t, 1);
    result = d_tm.mk_term(expr::TERM_EQ, to_term(child1), to_term(child2));
  } else if (msat_term_is_leq(d_env, t)) {
    msat_term child1 = msat_term_get_arg(t, 0);
    msat_term child2 = msat_term_get_arg(t, 1);
    result = d_tm.mk_term(expr::TERM_LEQ, to_term(child1), to_term(child2));
  } else if (msat_term_is_plus(d_env, t)) {
    size_t size = msat_term_arity(t);
    std::vector<expr::term_ref> children;
    for(size_t i = 0; i < size; ++ i) {
      msat_term child = msat_term_get_arg(t, i);
      children.push_back(to_term(child));
    }
    result = d_tm.mk_term(expr::TERM_ADD, children);
  } else if (msat_term_is_times(d_env, t)) {
    size_t size = msat_term_arity(t);
    std::vector<expr::term_ref> children;
    for(size_t i = 0; i < size; ++ i) {
      msat_term child = msat_term_get_arg(t, i);
      children.push_back(to_term(child));
    }
    result = d_tm.mk_term(expr::TERM_MUL, children);
  } else if (msat_term_is_bv_concat(d_env, t)) {
    size_t size = msat_term_arity(t);
    std::vector<expr::term_ref> children;
    for(size_t i = 0; i < size; ++ i) {
      msat_term child = msat_term_get_arg(t, i);
      children.push_back(to_term(child));
    }
    result = d_tm.mk_term(expr::TERM_BV_CONCAT, children);
  } else if (msat_term_is_bv_extract(d_env, t, &out_msb, &out_lsb)) {
    msat_term child = msat_term_get_arg(t, 0);
    result = d_tm.mk_bitvector_extract(to_term(child), expr::bitvector_extract(out_msb, out_lsb));
  } else if (msat_term_is_bv_or(d_env, t)) {
    size_t size = msat_term_arity(t);
    std::vector<expr::term_ref> children;
    for(size_t i = 0; i < size; ++ i) {
      msat_term child = msat_term_get_arg(t, i);
      children.push_back(to_term(child));
    }
    result = d_tm.mk_term(expr::TERM_BV_OR, children);
  } else if (msat_term_is_bv_xor(d_env, t)) {
    size_t size = msat_term_arity(t);
    std::vector<expr::term_ref> children;
    for(size_t i = 0; i < size; ++ i) {
      msat_term child = msat_term_get_arg(t, i);
      children.push_back(to_term(child));
    }
    result = d_tm.mk_term(expr::TERM_BV_XOR, children);
  } else if (msat_term_is_bv_and(d_env, t)) {
    size_t size = msat_term_arity(t);
    std::vector<expr::term_ref> children;
    for(size_t i = 0; i < size; ++ i) {
      msat_term child = msat_term_get_arg(t, i);
      children.push_back(to_term(child));
    }
    result = d_tm.mk_term(expr::TERM_BV_AND, children);
  } else if (msat_term_is_bv_not(d_env, t)) {
    msat_term child = msat_term_get_arg(t, 0);
    result = d_tm.mk_term(expr::TERM_BV_NOT, to_term(child));
  } else if (msat_term_is_bv_plus(d_env, t)) {
    size_t size = msat_term_arity(t);
    std::vector<expr::term_ref> children;
    for(size_t i = 0; i < size; ++ i) {
      msat_term child = msat_term_get_arg(t, i);
      children.push_back(to_term(child));
    }
    result = d_tm.mk_term(expr::TERM_BV_ADD, children);
  } else if (msat_term_is_bv_minus(d_env, t)) {
    msat_term child1 = msat_term_get_arg(t, 0);
    msat_term child2 = msat_term_get_arg(t, 1);
    result = d_tm.mk_term(expr::TERM_BV_SUB, to_term(child1), to_term(child2));
  } else if (msat_term_is_bv_times(d_env, t)) {
    size_t size = msat_term_arity(t);
    std::vector<expr::term_ref> children;
    for(size_t i = 0; i < size; ++ i) {
      msat_term child = msat_term_get_arg(t, i);
      children.push_back(to_term(child));
    }
    result = d_tm.mk_term(expr::TERM_BV_MUL, children);
  } else if (msat_term_is_bv_neg(d_env, t)) {
    msat_term child = msat_term_get_arg(t, 0);
    result = d_tm.mk_term(expr::TERM_BV_SUB, to_term(child));
  } else if (msat_term_is_bv_udiv(d_env, t)) {
    msat_term child1 = msat_term_get_arg(t, 0);
    msat_term child2 = msat_term_get_arg(t, 1);
    result = d_tm.mk_term(expr::TERM_BV_UDIV, to_term(child1), to_term(child2));
  } else if (msat_term_is_bv_urem(d_env, t)) {
    msat_term child1 = msat_term_get_arg(t, 0);
    msat_term child2 = msat_term_get_arg(t, 1);
    result = d_tm.mk_term(expr::TERM_BV_UREM, to_term(child1), to_term(child2));
  } else if (msat_term_is_bv_sdiv(d_env, t)) {
    msat_term child1 = msat_term_get_arg(t, 0);
    msat_term child2 = msat_term_get_arg(t, 1);
    result = d_tm.mk_term(expr::TERM_BV_SDIV, to_term(child1), to_term(child2));
  } else if (msat_term_is_bv_srem(d_env, t)) {
    msat_term child1 = msat_term_get_arg(t, 0);
    msat_term child2 = msat_term_get_arg(t, 1);
    result = d_tm.mk_term(expr::TERM_BV_SREM, to_term(child1), to_term(child2));
  } else if (msat_term_is_bv_ult(d_env, t)) {
    msat_term child1 = msat_term_get_arg(t, 0);
    msat_term child2 = msat_term_get_arg(t, 1);
    result = d_tm.mk_term(expr::TERM_BV_ULT, to_term(child1), to_term(child2));
  } else if (msat_term_is_bv_uleq(d_env, t)) {
    msat_term child1 = msat_term_get_arg(t, 0);
    msat_term child2 = msat_term_get_arg(t, 1);
    result = d_tm.mk_term(expr::TERM_BV_ULEQ, to_term(child1), to_term(child2));
  } else if (msat_term_is_bv_slt(d_env, t)) {
    msat_term child1 = msat_term_get_arg(t, 0);
    msat_term child2 = msat_term_get_arg(t, 1);
    result = d_tm.mk_term(expr::TERM_BV_SLT, to_term(child1), to_term(child2));
  } else if (msat_term_is_bv_sleq(d_env, t)) {
    msat_term child1 = msat_term_get_arg(t, 0);
    msat_term child2 = msat_term_get_arg(t, 1);
    result = d_tm.mk_term(expr::TERM_BV_SLEQ, to_term(child1), to_term(child2));
  } else if (msat_term_is_bv_lshl(d_env, t)) {
    msat_term child1 = msat_term_get_arg(t, 0);
    msat_term child2 = msat_term_get_arg(t, 1);
    result = d_tm.mk_term(expr::TERM_BV_SHL, to_term(child1), to_term(child2));
  } else if (msat_term_is_bv_lshr(d_env, t)) {
    msat_term child1 = msat_term_get_arg(t, 0);
    msat_term child2 = msat_term_get_arg(t, 1);
    result = d_tm.mk_term(expr::TERM_BV_LSHR, to_term(child1), to_term(child2));
  } else if (msat_term_is_bv_ashr(d_env, t)) {
    msat_term child1 = msat_term_get_arg(t, 0);
    msat_term child2 = msat_term_get_arg(t, 1);
    result = d_tm.mk_term(expr::TERM_BV_ASHR, to_term(child1), to_term(child2));
  } else if (msat_term_is_bv_zext(d_env, t, &out_amount)) {
  } else if (msat_term_is_bv_sext(d_env, t, &out_amount)) {
  } else if (msat_term_is_bv_rol(d_env, t, &out_amount)) {
  } else if (msat_term_is_bv_ror(d_env, t, &out_amount)) {
  } else if (msat_term_is_bv_comp(d_env, t)) {
    msat_term child1 = msat_term_get_arg(t, 0);
    msat_term child2 = msat_term_get_arg(t, 1);
    result = d_tm.mk_term(expr::TERM_EQ, to_term(child1), to_term(child2));
    result = d_tm.mk_term(expr::TERM_ITE, result, d_bv1, d_bv0);
  }

  // At this point we need to be non-null
  if (result.is_null()) {
    throw exception("Mathsat error (term creation)");
  }

  // Set the cache ref -> result
  d_term_cache->set_term_cache(t, result);

  return result;
}

void mathsat5_internal::add(expr::term_ref ref, solver::formula_class f_class) {

  // The mathsat version
  msat_term m_term = to_mathsat5_term(ref);
  if (d_assertion_map.find(m_term) != d_assertion_map.end()) {
    // Already asserted
    return;
  }

  // Remember the assertions
  expr::term_ref_strong ref_strong(d_tm, ref);
  d_assertions.push_back(ref_strong);
  d_assertion_classes.push_back(f_class);
  d_assertions_mathsat.push_back(m_term);
  d_assertion_map[m_term] = ref;

  // Get the interpolation group
  int itp_group = f_class == solver::CLASS_B ? d_itp_B : d_itp_A;

  // Set the interpolation group
  msat_set_itp_group(d_env, itp_group);

  // Assert to mathsat5
  if (output::trace_tag_is_enabled("mathsat5")) {
    char* str = msat_term_repr(m_term);
    TRACE("mathsat5") << "msat_term: " << str << std::endl;
    msat_free(str);
  }

  int ret = msat_assert_formula(d_env, m_term);
  if (ret != 0) {
    throw exception("MathSAT5 error (add).");
  }

  d_last_check_status = MSAT_UNKNOWN;
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

void mathsat5_internal::check_model() {
  std::cerr << "Checking model" << std::endl;
  assert(d_last_check_status == MSAT_SAT);

  // Check the mathsat model
  size_t num_asserted;
  msat_term* assertions = msat_get_asserted_formulas(d_env, &num_asserted);
  for (size_t i = 0; i < num_asserted; ++ i) {
    if (msat_term_id(assertions[i]) != msat_term_id(d_assertions_mathsat[i])) {
      throw exception("Mathsat internal assertions don't match external ones!");
    }
    msat_term value = msat_get_model_value(d_env, assertions[i]);
    if (!msat_term_is_true(d_env, value)) {
      throw exception("Check error: an assertion is false in the obtained mathsat model!");
    }
  }

  // Get the model
  expr::model::ref m = get_model();

  // Go through the assertions and evaluate
  for (size_t i = 0; i < d_assertions.size(); ++ i) {
    if (!m->is_true(d_assertions[i])) {
      throw exception("Check error: an assertion is false in the obtained model!");
    }
  }
}

expr::model::ref mathsat5_internal::get_model() {

  assert(d_last_check_status == MSAT_SAT);

  // Clear any data already there
  expr::model::ref m = new expr::model(d_tm, false);

  // Get the model from mathsat
  for (size_t i = 0; i < d_variables.size(); ++ i) {
    expr::term_ref var = d_variables[i];
    expr::term_ref var_type = d_tm.type_of(var);
    expr::value var_value;

    msat_term m_var = to_mathsat5_term(var);
    msat_term m_value = msat_get_model_value(d_env, m_var);
    assert(!MSAT_ERROR_TERM(m_value));

    switch (d_tm.term_of(var_type).op()) {
    case expr::TYPE_BOOL: {
      assert(msat_term_is_true(d_env, m_value) || msat_term_is_false(d_env, m_value));
      var_value = expr::value(msat_term_is_true(d_env, m_value));
      break;
    }
    case expr::TYPE_INTEGER: {
      assert(msat_term_is_number(d_env, m_value));
      mpq_t value_q;
      mpq_init(value_q);
      msat_term_to_number(d_env, m_value, value_q);
      // The rational
      var_value = expr::value(expr::rational(value_q));
      assert(var_value.get_rational().is_integer());
      // Clear the temps
      mpq_clear(value_q);
      break;
    }
    case expr::TYPE_REAL: {
      assert(msat_term_is_number(d_env, m_value));
      mpq_t value;
      mpq_init(value);
      msat_term_to_number(d_env, m_value, value);
      var_value = expr::value(expr::rational(value));
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
      var_value = expr::value(bv_value);
      // Clear the temps
      mpq_clear(value_q);
      break;
    }
    default:
      assert(false);
    }

    // Add the association
    m->set_variable_value(var, var_value);
  }

  return m;
}

void mathsat5_internal::interpolate(std::vector<expr::term_ref>& projection_out) {
  int itp_classes[1] = { d_itp_A };
  msat_term I = msat_get_interpolant(d_env, itp_classes, 1);
  if (MSAT_ERROR_TERM(I)) {
    if (output::trace_tag_is_enabled("mathsat5::interpolation")) {
      std::cerr << "Error while interpolating:" << std::endl;
      for (size_t i = 0; i < d_assertions.size(); ++ i) {
        std::cerr << "[" << i << "]: " << d_assertion_classes[i] << " " << d_assertions[i] << std::endl;
      }
    }
    std::stringstream ss;
    ss << "MathSAT interpolation error: " << msat_last_error_message(d_env);
    throw exception(std::string(ss.str()));
  }
  projection_out.push_back(to_term(I));
}

struct msat_term_cmp {
  bool operator () (const msat_term& t1, const msat_term& t2) const {
    return msat_term_id(t1) < msat_term_id(t2);
  }
};

void mathsat5_internal::get_unsat_core(std::vector<expr::term_ref>& out) {
  size_t core_size = 0;
  msat_term* core = msat_get_unsat_core(d_env, &core_size);
  if (core == 0 || core_size == 0) {
    throw exception("MathSAT unsat core error.");
  }

  // Output them
  for (size_t i = 0; i < core_size; ++ i) {
    assert(d_assertion_map.find(core[i]) != d_assertion_map.end());
    out.push_back(d_assertion_map[core[i]]);
  }

  // Free the core
  msat_free(core);
}

void mathsat5_internal::generalize(solver::generalization_type type, const std::set<expr::term_ref>& vars_to_keep, const std::set<expr::term_ref>& vars_to_elim, std::vector<expr::term_ref>& out) {

  expr::model::ref m = get_model();

  if (d_opts.get_bool("mathsat5-generalize-qe")) {

    // QE:
    // A if forward,
    // B if backward
    // T always
    std::vector<expr::term_ref> assertions_for_qe;
    for (size_t i = 0; i < d_assertions.size(); ++ i) {
      switch (d_assertion_classes[i]) {
      case solver::CLASS_A:
        if (type == solver::GENERALIZE_FORWARD) {
          assertions_for_qe.push_back(d_assertions[i]);
        }
        break;
      case solver::CLASS_T:
        assertions_for_qe.push_back(d_assertions[i]);
        break;
      case solver::CLASS_B:
        assertions_for_qe.push_back(d_assertions[i]);
        break;
      }
    }

    // The formula to eliminate
    expr::term_ref f_to_eliminate = d_tm.mk_and(assertions_for_qe);
    msat_term f_msat = to_mathsat5_term(f_to_eliminate);

    // Variables to eliminate
    msat_term vars_msat[vars_to_elim.size()];
    std::set<expr::term_ref>::const_iterator it = vars_to_elim.begin(), it_end = vars_to_elim.end();
    for (size_t i = 0; it != it_end; ++ it, ++ i) {
      vars_msat[i] = to_mathsat5_term(*it);
    }

    // Eliminate
    msat_exist_elim_options opts;
    opts.boolean_simplifications = true;
    opts.remove_redundant_constraints = true;
    opts.toplevel_propagation = true;
    msat_term msat_result = msat_exist_elim(d_env, f_msat, vars_msat, vars_to_elim.size(), MSAT_EXIST_ELIM_ALLSMT_FM, opts);

    // Add to result
    expr::term_ref result = to_term(msat_result);
    out.push_back(result);

  } else if (d_opts.get_bool("mathsat5-generalize-trivial")) {
    std::set<expr::term_ref>::const_iterator it = vars_to_keep.begin(), it_end = vars_to_keep.end();
    for (; it != it_end; ++it) {
      // var = value
      expr::term_ref var = *it;
      assert(m->has_value(var));
      expr::term_ref value = m->get_term_value(var).to_term(d_tm);

      if (d_tm.type_of(var) == d_tm.boolean_type()) {
        if (d_tm.get_boolean_constant(d_tm.term_of(value))) {
          out.push_back(var);
        } else {
          out.push_back(d_tm.mk_term(expr::TERM_NOT, var));
        }
      } else {
        out.push_back(d_tm.mk_term(expr::TERM_EQ, var, value));
      }
    }
  } else {
    throw exception("Generalization not supported!");
  }
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
    d_assertion_map.erase(d_assertions_mathsat.back());
    d_assertions.pop_back();
    d_assertions_mathsat.pop_back();
    d_assertion_classes.pop_back();
  }
  d_last_check_status = MSAT_UNKNOWN;
}

void mathsat5_internal::gc() {
  d_term_cache->gc();
}

void mathsat5_internal::gc_collect(const expr::gc_relocator& gc_reloc) {
  gc_reloc.reloc(d_assertions);
  gc_reloc.reloc(d_bv1);
  gc_reloc.reloc(d_bv0);
  gc_reloc.reloc(d_variables);
}

mathsat5::mathsat5(expr::term_manager& tm, const options& opts, utils::statistics& stats)
: solver("mathsat5", tm, opts, stats)
{
  d_internal = new mathsat5_internal(tm, opts);
}

mathsat5::~mathsat5() {
  delete d_internal;
}

void mathsat5::add(expr::term_ref f, formula_class f_class) {
  TRACE("mathsat5") << "mathsat5[" << d_internal->instance() << "]: adding " << f << " in " << f_class << std::endl;
  d_internal->add(f, f_class);
}

solver::result mathsat5::check() {
  TRACE("mathsat5") << "mathsat5[" << d_internal->instance() << "]: check()" << std::endl;
  return d_internal->check();
}

void mathsat5::check_model() {
  TRACE("mathsat5") << "mathsat5[" << d_internal->instance() << "]: check_model()" << std::endl;
  d_internal->check_model();
}

expr::model::ref mathsat5::get_model() const {
  TRACE("mathsat5") << "mathsat5[" << d_internal->instance() << "]: get_model()" << std::endl;
  return d_internal->get_model();
}

void mathsat5::push() {
  TRACE("mathsat5") << "mathsat5[" << d_internal->instance() << "]: push()" << std::endl;
  d_internal->push();
}

void mathsat5::pop() {
  TRACE("mathsat5") << "mathsat5[" << d_internal->instance() << "]: pop()" << std::endl;
  d_internal->pop();
}

/** Interpolate the last sat result (trivial) */
void mathsat5::generalize(generalization_type type, std::vector<expr::term_ref>& out) {
  TRACE("mathsat5") << "mathsat5[" << d_internal->instance() << "]: interpolating" << std::endl;
  switch (type) {
  case GENERALIZE_FORWARD:
    d_internal->generalize(type, d_B_variables, d_A_variables, out);
    break;
  case GENERALIZE_BACKWARD:
    d_internal->generalize(type, d_A_variables, d_B_variables, out);
  }

}


void mathsat5::interpolate(std::vector<expr::term_ref>& out) {
  TRACE("mathsat5") << "mathsat5[" << d_internal->instance() << "]: interpolating" << std::endl;
  d_internal->interpolate(out);
}

void mathsat5::get_unsat_core(std::vector<expr::term_ref>& out) {
  TRACE("mathsat5") << "mathsat5[" << d_internal->instance() << "]: unsat core" << std::endl;
  d_internal->get_unsat_core(out);
}

bool mathsat5::supports(solver::feature f) const {
  return d_internal->supports(f);
}

void mathsat5::gc() {
  d_internal->gc();
}

void mathsat5::gc_collect(const expr::gc_relocator& gc_reloc) {
  solver::gc_collect(gc_reloc);
  d_internal->gc_collect(gc_reloc);
}

}
}

#endif
