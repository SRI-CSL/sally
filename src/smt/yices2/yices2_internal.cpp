/*
 * yices2_internal.cpp
 *
 *  Created on: Apr 8, 2015
 *      Author: dejan
 */

#ifdef WITH_YICES2

#include "smt/yices2/yices2_internal.h"
#include "smt/yices2/yices2_term_cache.h"
#include "utils/trace.h"

#include <iostream>

namespace sally {
namespace smt {

int yices2_internal::s_instances = 0;

type_t yices2_internal::s_bool_type = NULL_TYPE;
type_t yices2_internal::s_int_type = NULL_TYPE;
type_t yices2_internal::s_real_type = NULL_TYPE;

yices2_internal::yices2_internal(expr::term_manager& tm, const options& opts)
: d_tm(tm)
, d_conversion_cache(0)
, d_last_check_status(STATUS_UNKNOWN)
, d_config(NULL)
, d_instance(s_instances)
{
  // Initialize
  if (s_instances == 0) {
    TRACE("yices2") << "yices2: first instance." << std::endl;

    // Initialize it
    yices_init();

    // The basic types
    s_bool_type = yices_bool_type();
    s_int_type = yices_int_type();
    s_real_type = yices_real_type();
  }
  s_instances ++;
  d_conversion_cache = yices2_term_cache::get_cache(tm);

  // Bitvector bits
  d_bv0 = expr::term_ref_strong(d_tm, d_tm.mk_bitvector_constant(expr::bitvector(1, 0)));
  d_bv1 = expr::term_ref_strong(d_tm, d_tm.mk_bitvector_constant(expr::bitvector(1, 1)));

  // The context
  if (opts.has_option("solver-logic")) {
    d_config = yices_new_config();
    int32_t ret = yices_default_config_for_logic(d_config, opts.get_string("solver-logic").c_str());
    if (ret < 0) {
      std::stringstream ss;
      char* error = yices_error_string();
      ss << "Yices error (configuration creation): " << error;
      throw exception(ss.str());
    }
  }
  d_ctx = yices_new_context(d_config);
  if (d_ctx == 0) {
    std::stringstream ss;
    char* error = yices_error_string();
    ss << "Yices error (context creation): " << error;
    throw exception(ss.str());
  }
}

yices2_internal::~yices2_internal() {

  // The context
  yices_free_context(d_ctx);

  // The config
  if (d_config) {
    yices_free_config(d_config);
  }

  // Cleanup if the last one
  s_instances--;
  if (s_instances == 0) {
    TRACE("yices2") << "yices2: last instance removed." << std::endl;
    // Delete yices
    yices_exit();
    // Clear the cache
    d_conversion_cache->clear();
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
  case expr::TERM_BV_ADD:
    assert(n == 2);
    result = yices_bvadd(children[0], children[1]);
    break;
  case expr::TERM_BV_SUB:
    if (n == 1) {
      result = yices_bvneg(children[0]);
    } else {
      result = yices_bvsub(children[0], children[1]);
    }
    break;
  case expr::TERM_BV_MUL:
    assert(n == 2);
    result = yices_bvmul(children[0], children[1]);
    break;
  case expr::TERM_BV_UDIV: // NOTE: semantics of division is x/0 = 111...111
    assert(n == 2);
    result = yices_bvdiv(children[0], children[1]);
    break;
  case expr::TERM_BV_SDIV:
    assert(n == 2);
    result = yices_bvsdiv(children[0], children[1]);
    break;
  case expr::TERM_BV_UREM:
    assert(n == 2);
    result = yices_bvrem(children[0], children[1]);
    break;
  case expr::TERM_BV_SREM:
    assert(n == 2);
    result = yices_bvsrem(children[0], children[1]);
    break;
  case expr::TERM_BV_SMOD:
    assert(n == 2);
    result = yices_bvsmod(children[0], children[1]);
    break;
  case expr::TERM_BV_XOR:
    result = yices_bvxor(n, children);
    break;
  case expr::TERM_BV_SHL:
    assert(n == 2);
    result = yices_bvshl(children[0], children[1]);
    break;
  case expr::TERM_BV_LSHR:
    assert(n == 2);
    result = yices_bvlshr(children[0], children[1]);
    break;
  case expr::TERM_BV_ASHR:
    assert(n == 2);
    result = yices_bvashr(children[0], children[1]);
    break;
  case expr::TERM_BV_NOT:
    assert(n == 1);
    result = yices_bvnot(children[0]);
    break;
  case expr::TERM_BV_AND:
    result = yices_bvand(n, children);
    break;
  case expr::TERM_BV_OR:
    result = yices_bvor(n, children);
    break;
  case expr::TERM_BV_NAND:
    assert(n == 2);
    result = yices_bvnand(children[0], children[1]);
    break;
  case expr::TERM_BV_NOR:
    assert(n == 2);
    result = yices_bvnor(children[0], children[1]);
    break;
  case expr::TERM_BV_XNOR:
    assert(n == 2);
    result = yices_bvxnor(children[0], children[1]);
    break;
  case expr::TERM_BV_CONCAT:
    result = yices_bvconcat(n, children);
    break;
  case expr::TERM_BV_ULEQ:
    assert(n == 2);
    result = yices_bvle_atom(children[0], children[1]);
    break;
  case expr::TERM_BV_SLEQ:
    assert(n == 2);
    result = yices_bvsle_atom(children[0], children[1]);
    break;
  case expr::TERM_BV_ULT:
    assert(n == 2);
    result = yices_bvlt_atom(children[0], children[1]);
    break;
  case expr::TERM_BV_SLT:
    assert(n == 2);
    result = yices_bvslt_atom(children[0], children[1]);
    break;
  case expr::TERM_BV_UGEQ:
    assert(n == 2);
    result = yices_bvge_atom(children[0], children[1]);
    break;
  case expr::TERM_BV_SGEQ:
    assert(n == 2);
    result = yices_bvsge_atom(children[0], children[1]);
    break;
  case expr::TERM_BV_UGT:
    assert(n == 2);
    result = yices_bvgt_atom(children[0], children[1]);
    break;
  case expr::TERM_BV_SGT:
    assert(n == 2);
    result = yices_bvsgt_atom(children[0], children[1]);
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
    result = s_bool_type;
    break;
  case expr::TYPE_INTEGER:
    result = s_int_type;
    break;
  case expr::TYPE_REAL:
    result = s_real_type;
    break;
  case expr::TYPE_BITVECTOR: {
    size_t size = d_tm.get_bitvector_type_size(ref);
    result = yices_bv_type(size);
    break;
  }
  default:
    assert(false);
  }

  return result;
}

term_t yices2_internal::to_yices2_term(expr::term_ref ref) {

  term_t result = NULL_TERM;

  // Check the term has been translated already
  result = d_conversion_cache->get_term_cache(ref);
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
  case expr::CONST_BITVECTOR: {
    expr::bitvector bv = d_tm.get_bitvector_constant(t);
    result = yices_bvconst_mpz(bv.size(), bv.mpz().get_mpz_t());
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
      children[i] = to_yices2_term(t[i]);
    }
    result = mk_yices2_term(t.op(), size, children);
    break;
  }
  case expr::TERM_BV_EXTRACT: {
    const expr::bitvector_extract& extract = d_tm.get_bitvector_extract(t);
    term_t child = to_yices2_term(t[0]);
    result = yices_bvextract(child, extract.low, extract.high);
    break;
  }
  default:
    assert(false);
  }

  if (result < 0) {
    std::stringstream ss;
    char* error = yices_error_string();
    ss << "Yices error (term creation): " << error;
    throw exception(ss.str());
  }

  // Set the cache ref -> result
  d_conversion_cache->set_term_cache(ref, result);

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
  delete[] bits_str;
  return bv;
}

expr::term_ref yices2_internal::to_term(term_t t) {

  expr::term_ref result;

  // Check the cache
  result = d_conversion_cache->get_term_cache(t);
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
    delete[] bits;
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
    delete[] a_i_bits;
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
    std::stringstream ss;
    char* error = yices_error_string();
    ss << "Yices error (term creation): " << error;
    throw exception(ss.str());
  }

  // Set the cache ref -> result
  d_conversion_cache->set_term_cache(result, t);

  return result;
}

void yices2_internal::add(expr::term_ref ref, solver::formula_class f_class) {
  // Remember the assertions
  expr::term_ref_strong ref_strong(d_tm, ref);
  d_assertions.push_back(ref_strong);
  d_assertion_classes.push_back(f_class);

  // Assert to yices
  term_t yices_term = to_yices2_term(ref);
  if (output::trace_tag_is_enabled("yices2")) {
    yices_pp_term(stderr, yices_term, 80, 100, 0);
  }
  int ret = yices_assert_formula(d_ctx, yices_term);
  if (ret < 0) {
    std::stringstream ss;
    char* error = yices_error_string();
    ss << "Yices error (add): " << error;
    throw exception(ss.str());
  }
}

solver::result yices2_internal::check() {
  d_last_check_status = yices_check_context(d_ctx, 0);

  switch (d_last_check_status) {
  case STATUS_SAT:
    return solver::SAT;
  case STATUS_UNSAT:
    return solver::UNSAT;
  case STATUS_UNKNOWN:
    return solver::UNKNOWN;
  default: {
    std::stringstream ss;
    char* error = yices_error_string();
    ss << "Yices error (check): " << error;
    throw exception(ss.str());
  }
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
  delete[] value_str;
  return bv;
}

void yices2_internal::get_model(expr::model& m, const std::set<expr::term_ref>& x_variables, const std::set<expr::term_ref>& y_variables) {
  assert(d_last_check_status == STATUS_SAT);
  assert(x_variables.size() > 0 || y_variables.size() > 0);

  // Clear any data already there
  m.clear();

  // Get the model from yices
  model_t* yices_model = yices_get_model(d_ctx, true);

  if (output::trace_tag_is_enabled("yices2")) {
    yices_pp_model(stderr, yices_model, 80, 100, 0);
  }

  // Get the variables
  std::vector<expr::term_ref> variables;
  bool class_A_used = false;
  bool class_B_used = false;
  for (size_t i = 0; i < d_assertion_classes.size(); ++ i) {
    switch (d_assertion_classes[i]) {
    case solver::CLASS_A:
      class_A_used = true;
      break;
    case solver::CLASS_B:
      class_B_used = true;
      break;
    case solver::CLASS_T:
      class_A_used = true;
      class_B_used = true;
      break;
    default:
      assert(false);
    }
  }

  if (class_A_used) {
    variables.insert(variables.end(), x_variables.begin(), x_variables.end());
  }
  if (class_B_used) {
    variables.insert(variables.end(), y_variables.begin(), y_variables.end());
  }

  // See which variables we have to reason about
  for (size_t i = 0; i < variables.size(); ++ i) {
    expr::term_ref var = variables[i];
    term_t yices_var = to_yices2_term(var);
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
      expr::integer integer_value(value);
      var_value = d_tm.mk_integer_constant(integer_value);
      // Clear the temps
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
      delete[] value;
      break;
    }
    default:
      assert(false);
    }

    // Add the association
    m.set_variable_value(var, var_value);
  }

  // Free the yices model
  yices_free_model(yices_model);
}

void yices2_internal::push() {
  int ret = yices_push(d_ctx);
  if (ret < 0) {
    std::stringstream ss;
    char* error = yices_error_string();
    ss << "Yices error (push): " << error;
    yices_free_string(error);
    throw exception(ss.str());
  }
  d_assertions_size.push_back(d_assertions.size());
}

void yices2_internal::pop() {
  int ret = yices_pop(d_ctx);
  if (ret < 0) {
    std::stringstream ss;
    char* error = yices_error_string();
    ss << "Yices error (pop): " << error;
    throw exception(ss.str());
  }
  size_t size = d_assertions_size.back();
  d_assertions_size.pop_back();
  while (d_assertions.size() > size) {
    d_assertions.pop_back();
    d_assertion_classes.pop_back();
  }
}

void yices2_internal::generalize(smt::solver::generalization_type type, const std::set<expr::term_ref>& to_eliminate, std::vector<expr::term_ref>& projection_out) {

  assert(!to_eliminate.empty());
  assert(!d_assertions.empty());

  // Get the model
  model_t* m = yices_get_model(d_ctx, true);

  if (output::trace_tag_is_enabled("yices2")) {
    std::cerr << "model:" << std::endl;
    yices_pp_model(stderr, m, 80, 100, 0);
  }

  // Copy over A formulas and count the rest
  size_t to_generalize = 0;
  for (size_t i = 0; i < d_assertions.size(); ++ i) {
    if (d_assertion_classes[i] != solver::CLASS_A) {
      to_generalize ++;
    }
  }

  // Yices version of the assertions
  term_t* assertions = new term_t[to_generalize];
  size_t j = 0;
  // Add class B first
  switch (type) {
  case smt::solver::GENERALIZE_BACKWARD:
    for (size_t i = 0; i < d_assertions.size(); ++ i) {
      if (d_assertion_classes[i] == solver::CLASS_B) {
        assertions[j++] = to_yices2_term(d_assertions[i]);
      }
    }
    break;
  case smt::solver::GENERALIZE_FORWARD:
    for (size_t i = 0; i < d_assertions.size(); ++ i) {
      if (d_assertion_classes[i] == solver::CLASS_A) {
        assertions[j++] = to_yices2_term(d_assertions[i]);
      }
    }
    break;
  default:
    assert(false);
  }

  // Add class T
  for (size_t i = 0; i < d_assertions.size(); ++ i) {
    if (d_assertion_classes[i] == solver::CLASS_T) {
      assertions[j++] = to_yices2_term(d_assertions[i]);
    }
  }

  // Yices version of the variables
  term_t* variables = new term_t[to_eliminate.size()];
  std::set<expr::term_ref>::const_iterator it = to_eliminate.begin(), it_end = to_eliminate.end();
  for (size_t i = 0; it != it_end; ++ i, ++ it) {
    variables[i] = to_yices2_term(*it);
  }

  if (output::trace_tag_is_enabled("yices2")) {
    std::cerr << "assertions:" << std::endl;
    for (size_t i = 0; i < to_generalize; ++ i) {
      std::cerr << i << ": ";
      yices_pp_term(stderr, assertions[i], 80, 100, 0);
    }
    std::cerr << "variables:" << std::endl;
    for (size_t i = 0; i < to_eliminate.size(); ++ i) {
      std::cerr << i << ": ";
      yices_pp_term(stdout, variables[i], 80, 100, 0);
    }
  }

  // Generalize
  term_vector_t G_y;
  yices_init_term_vector(&G_y);
  int32_t ret = yices_generalize_model_array(m, to_generalize, assertions, to_eliminate.size(), variables, YICES_GEN_DEFAULT, &G_y);
  if (ret < 0) {
    throw exception("Generalization failed in Yices.");
  }
  for (size_t i = 0; i < G_y.size; ++ i) {
    projection_out.push_back(to_term(G_y.data[i]));
  }
  yices_delete_term_vector(&G_y);

  if (output::trace_tag_is_enabled("yices2")) {
    std::cerr << "generalization: " << std::endl;
    for (size_t i = 0; i < projection_out.size(); ++ i) {
      std::cerr << i << ": " << projection_out[i] << std::endl;
    }
  }

  // Free temps
  delete[] variables;
  delete[] assertions;
  yices_free_model(m);
}

void yices2_internal::gc() {
  d_conversion_cache->gc();
}

void yices2_internal::get_assertions(std::set<expr::term_ref>& out) const {
  for (size_t i = 0; i < d_assertions.size(); ++ i) {
    out.insert(d_assertions[i]);
  }
}

void yices2_internal::add_x_variable(expr::term_ref x_var) {
  d_variables.push_back(x_var);
}

void yices2_internal::add_y_variable(expr::term_ref y_var) {
  d_variables.push_back(y_var);
}

}
}

#endif
