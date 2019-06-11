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

#ifdef WITH_YICES2

#ifdef WITH_LIBPOLY
#include "poly/rational.h"
#include "poly/algebraic_number.h"
#endif
#include "smt/yices2/yices2_internal.h"
#include "smt/yices2/yices2_term_cache.h"
#include "utils/trace.h"
#include "expr/gc_relocator.h"
#include "expr/term_visitor.h"
#include "utils/output.h"

#include <iostream>
#include <fstream>

namespace sally {
namespace smt {

int yices2_internal::s_instances = 0;

type_t yices2_internal::s_bool_type = NULL_TYPE;
type_t yices2_internal::s_int_type = NULL_TYPE;
type_t yices2_internal::s_real_type = NULL_TYPE;

std::string  yices2_internal::yices_error(void) {
  char* yerror = yices_error_string();
  std::string retval(yerror);
  yices_free_string(yerror);
  return retval;
}

  
void yices2_internal::check_error(int ret, const char* error_msg) const {
  if (ret < 0) {
    std::stringstream ss;
    ss << error_msg << ": " << yices_error();
    throw exception(ss.str());
  }
}

yices2_internal::yices2_internal(expr::term_manager& tm, const options& opts)
: d_tm(tm)
, d_ctx_dpllt(NULL)
, d_ctx_mcsat(NULL)
, d_dpllt_incomplete(false)
, d_mcsat_incomplete(false)
, d_conversion_cache(0)
, d_last_check_status_dpllt(STATUS_UNKNOWN)
, d_last_check_status_mcsat(STATUS_UNKNOWN)
, d_config_dpllt(NULL)
, d_config_mcsat(NULL)
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
  int32_t ret = 0; 

  std::string mode = "hybrid";
  if (opts.has_option("yices2-mode")) {
    mode = opts.get_string("yices2-mode");
  }
  bool use_dpllt = mode == "dpllt" || mode == "hybrid";
  bool use_mcsat = mode == "mcsat" || mode == "hybrid";
  if (!use_dpllt && !use_mcsat) {
    throw exception("yices2-mode must be one of dpllt, mcsat, or hybrid (got " + mode + ")");
  }

  if (use_dpllt) {
    d_config_dpllt = yices_new_config();
    if (opts.has_option("solver-logic")) {
      ret = yices_default_config_for_logic(d_config_dpllt, opts.get_string("solver-logic").c_str());
      check_error(ret, "Yices error (default configuration creation)");
    }
    if (opts.has_option("yices2-trace-tags")) {
      ret = yices_set_config(d_config_dpllt, "trace", opts.get_string("yices2-trace-tags").c_str());
      check_error(ret, "Yices error (mcsat option)");
    }
    d_ctx_dpllt = yices_new_context(d_config_dpllt);
    if (d_ctx_dpllt == 0) {
      std::stringstream ss;
      ss << "Yices error (context creation): " << yices_error();
      throw exception(ss.str());
    }
  }
  if (use_mcsat) {
    d_config_mcsat = yices_new_config();
    if (opts.has_option("yices2-trace-tags")) {
      ret = yices_set_config(d_config_mcsat, "trace", opts.get_string("yices2-trace-tags").c_str());
      check_error(ret, "Yices error (mcsat option)");
    }
    ret = yices_set_config(d_config_mcsat, "solver-type", "mcsat");
    check_error(ret, "Yices error (mcsat option)");
    d_ctx_mcsat = yices_new_context(d_config_mcsat);
    if (d_ctx_mcsat == 0) {
      std::stringstream ss;
      ss << "Yices error (context creation): " << yices_error();
      throw exception(ss.str());
    }
  }
}

yices2_internal::~yices2_internal() {

  // The context
  if (d_ctx_dpllt) {
    yices_free_context(d_ctx_dpllt);
  }
  if (d_ctx_mcsat) {
    yices_free_context(d_ctx_mcsat);
  }

  // The config
  if (d_config_dpllt) {
    yices_free_config(d_config_dpllt);
  }
  if (d_config_mcsat) {
    yices_free_config(d_config_mcsat);
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
  case expr::TERM_TO_INT:
    assert(n == 1);
    result = yices_floor(children[0]);
    break;
  case expr::TERM_TO_REAL:
    assert(n == 1);
    result = children[0];
    break;
  case expr::TERM_IS_INT:
    assert(n == 1);
    result = yices_is_int_atom(children[0]);
    break;
  case expr::TERM_EQ:
    assert(n == 2);
    result = yices_eq(children[0], children[1]);
    break;
  case expr::TERM_ITE:
    assert(n == 3);
    result = yices_ite(children[0], children[1], children[2]);
    break;
  case expr::TERM_BV_ADD: {
    assert(n >= 2);
    result = yices_bvadd(children[0], children[1]);
    for (size_t i = 2; i < n; ++ i) {
      result = yices_bvadd(result, children[i]);
    }
    break;
  }
  case expr::TERM_BV_SUB:
    if (n == 1) {
      result = yices_bvneg(children[0]);
    } else {
      result = yices_bvsub(children[0], children[1]);
    }
    break;
  case expr::TERM_BV_MUL: {
    assert(n >= 2);
    result = yices_bvmul(children[0], children[1]);
    for (size_t i = 2; i < n; ++ i) {
      result = yices_bvmul(result, children[i]);
    }
    break;
  }
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

  if (result < 0) {
    std::stringstream ss;
    ss << "Yices error (term creation): " << yices_error() << " for op " << op << " and terms";
    for (size_t i = 0; i < n; ++ i) {
      char* str = yices_term_to_string(children[i], UINT32_MAX, UINT32_MAX, 0);
      if (i) { ss << ", "; }
      else {ss << " "; }
      ss << str;
      yices_free_string(str);
    }
    throw exception(ss.str());
  }

  return result;
}

type_t yices2_internal::to_yices2_type(expr::term_ref ref) {

  type_t result = NULL_TERM;

  expr::term_op op = d_tm.term_of(ref).op();
  switch (op) {
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

  if (result < 0) {
    std::stringstream ss;
    ss << "Yices error (term creation): " << yices_error();
    throw exception(ss.str());
  }

  return result;
}

class to_yices_visitor {

  expr::term_manager& d_tm;

  yices2_internal& d_yices;
  yices2_term_cache& d_conversion_cache;

public:

  to_yices_visitor(expr::term_manager& tm, yices2_internal& yices, yices2_term_cache& cache)
  : d_tm(tm)
  , d_yices(yices)
  , d_conversion_cache(cache)
  {}

  // Non-null terms are good
  bool is_good_term(expr::term_ref t) const {
    return !t.is_null();
  }

  // Get the children of t
  void get_children(expr::term_ref t, std::vector<expr::term_ref>& children) {
    const expr::term& t_term = d_tm.term_of(t);
    for (size_t i = 0; i < t_term.size(); ++ i) {
      children.push_back(t_term[i]);
    }
  }

  // We visit all regular nodes
  // the cache yet
  expr::visitor_match_result match(expr::term_ref t) {
    // Anything already in the cache should not be visited
    if (d_conversion_cache.get_term_cache(t) != NULL_TERM) {
      return expr::DONT_VISIT_AND_BREAK;
    }
    // Otherwise, visit any meaningful children
    expr::term_op op = d_tm.term_of(t).op();
    if (op == expr::VARIABLE) {
      // Don't go into the variable children (types)
      return expr::VISIT_AND_BREAK;
    } else {
      return expr::VISIT_AND_CONTINUE;
    }
  }

  void visit(expr::term_ref ref) {
    // At this point all the children are in the conversion cache
    term_t result = NULL_TERM;

    TRACE("yices2:to_yices") << "convert::visit(" << ref << ")" << std::endl;

    // The term
    const expr::term& t = d_tm.term_of(ref);
    expr::term_op t_op = t.op();

    switch (t_op) {
    case expr::VARIABLE:
      result = yices_new_uninterpreted_term(d_yices.to_yices2_type(t[0]));
      yices_set_term_name(result, d_tm.get_variable_name(t).c_str());
      break;
    case expr::CONST_BOOL:
      result = d_tm.get_boolean_constant(t) ? yices_true() : yices_false();
      break;
    case expr::CONST_RATIONAL:
      result = yices_mpq(d_tm.get_rational_constant(t).mpq().get_mpq_t());
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
    case expr::TERM_TO_INT:
    case expr::TERM_TO_REAL:
    case expr::TERM_IS_INT:
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
      term_t children[size];
      for (size_t i = 0; i < size; ++ i) {
        children[i] = d_conversion_cache.get_term_cache(t[i]);
      }
      result = d_yices.mk_yices2_term(t.op(), size, children);
      break;
    }
    case expr::TERM_BV_EXTRACT: {
      const expr::bitvector_extract& extract = d_tm.get_bitvector_extract(t);
      term_t child = d_conversion_cache.get_term_cache(t[0]);
      result = yices_bvextract(child, extract.low, extract.high);
      break;
    }
    default:
      assert(false);
    }

    if (result < 0) {
      std::stringstream ss;
      ss << "Yices error (term creation): " << yices2_internal::yices_error();
      throw exception(ss.str());
    }

    // Set the cache ref -> result
    d_conversion_cache.set_term_cache(ref, result);
  }
};

term_t yices2_internal::to_yices2_term(expr::term_ref ref) {
  to_yices_visitor visitor(d_tm, *this, *d_conversion_cache);
  expr::term_visit_topological<to_yices_visitor, expr::term_ref, expr::term_ref_hasher> topological_visit(visitor);
  topological_visit.run(ref);
  term_t result = d_conversion_cache->get_term_cache(ref);
  assert(result != NULL_TERM);
  return result;
}

expr::term_ref yices2_internal::bool_term_to_bv(expr::term_ref t) {
  if (d_tm.type_of(t) == d_tm.boolean_type()) {
    expr::term_ref result;
    switch (d_tm.term_of(t).op()) {
    case expr::CONST_BOOL:
      if (d_tm.get_boolean_constant(d_tm.term_of(t))) {
        result = d_bv1;
      } else {
        result = d_bv0;
      }
      break;
    case expr::TERM_NOT:
      result = d_tm.mk_term(expr::TERM_BV_NOT, bool_term_to_bv(d_tm.term_of(t)[0]));
      break;
    case expr::TERM_EQ: {
      // Catch cases like (extract[0] = 1), and replace with extract[0]
      const expr::term& t_eq = d_tm.term_of(t);
      if (t_eq[0] == d_bv0) {
        result = d_tm.mk_term(expr::TERM_BV_NOT, t_eq[1]);
      } else if (t_eq[0] == d_bv1) {
        result = t_eq[1];
      } else if (t_eq[1] == d_bv0) {
        result = d_tm.mk_term(expr::TERM_BV_NOT, t_eq[0]);
      } else if (t_eq[1] == d_bv1) {
        result = t_eq[0];
      } else {
        result = d_tm.mk_term(expr::TERM_ITE, t, d_bv1, d_bv0);
      }
      break;
    }
    case expr::TERM_ITE: {
      // Catch cases like (ITE (bit = 1) THEN 1 ELSE 0)
      const expr::term& t_ite = d_tm.term_of(t);
      if (t_ite[1] == d_bv1 && t_ite[2] == d_bv0) {
        const expr::term& cond = d_tm.term_of(t_ite[0]);
        if (cond.op() == expr::TERM_EQ && cond[1] == d_bv1) {
          result = cond[0];
        } else {
          result = d_tm.mk_term(expr::TERM_ITE, t, d_bv1, d_bv0);
        }
      } else {
        result = d_tm.mk_term(expr::TERM_ITE, t, d_bv1, d_bv0);
      }
      break;
    }
    default:
      result = d_tm.mk_term(expr::TERM_ITE, t, d_bv1, d_bv0);
    }
    return result;
  } else {
    return t;
  }
}

expr::term_ref yices2_internal::mk_term(term_constructor_t constructor, const std::vector<expr::term_ref>& children) {
  expr::term_ref result;

  switch (constructor) {
  case YICES_ITE_TERM:
    result = d_tm.mk_term(expr::TERM_ITE, children);
    break;
  case YICES_APP_TERM:
    assert(false);
    break;
  case YICES_UPDATE_TERM:
    assert(false);
    break;
  case YICES_TUPLE_TERM:
    assert(false);
    break;
  case YICES_EQ_TERM:
    result = d_tm.mk_term(expr::TERM_EQ, children);
    break;
  case YICES_DISTINCT_TERM:
    assert(false);
    break;
  case YICES_FORALL_TERM:
    assert(false);
    break;
  case YICES_LAMBDA_TERM:
    assert(false);
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
  case YICES_BV_ARRAY: {
    std::vector<expr::term_ref> bv_children;
    for (size_t i = 0; i < children.size(); ++ i) {
      bv_children.push_back(bool_term_to_bv(children[i]));
    }
    std::reverse(bv_children.begin(), bv_children.end());
    if (bv_children.size() > 1) {
      result = d_tm.mk_term(expr::TERM_BV_CONCAT, bv_children);
    } else {
      result = bv_children[0];
    }
    break;
  }
  case YICES_BV_DIV:
    result = d_tm.mk_term(expr::TERM_BV_UDIV, children);
    break;
  case YICES_BV_REM:
    result = d_tm.mk_term(expr::TERM_BV_UREM, children);
    break;
  case YICES_BV_SDIV:
    result = d_tm.mk_term(expr::TERM_BV_SDIV, children);
    break;
  case YICES_BV_SREM:
    result = d_tm.mk_term(expr::TERM_BV_SREM, children);
    break;
  case YICES_BV_SMOD:
    result = d_tm.mk_term(expr::TERM_BV_SMOD, children);
    break;
  case YICES_BV_SHL:
    result = d_tm.mk_term(expr::TERM_BV_SHL, children);
    break;
  case YICES_BV_LSHR:
    result = d_tm.mk_term(expr::TERM_BV_LSHR, children);
    break;
  case YICES_BV_ASHR:
    result = d_tm.mk_term(expr::TERM_BV_ASHR, children);
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
    assert(false);
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

class to_term_visitor {

  expr::term_manager& d_tm;

  yices2_internal& d_yices;
  yices2_term_cache& d_conversion_cache;

  expr::term_ref d_bv1;
  expr::term_ref d_bv0;

public:

  to_term_visitor(expr::term_manager& tm, yices2_internal& yices, yices2_term_cache& cache)
  : d_tm(tm)
  , d_yices(yices)
  , d_conversion_cache(cache)
  {
    d_bv0 = d_tm.mk_bitvector_constant(expr::bitvector(1, 0));
    d_bv1 = d_tm.mk_bitvector_constant(expr::bitvector(1, 1));
  }

  // Non-null terms are good
  bool is_good_term(term_t t) const {
    return t != NULL_TERM;
  }

  // Get the children of t
  void get_children(term_t t, std::vector<term_t>& children) {
    term_constructor_t t_constructor = yices_term_constructor(t);
    switch (t_constructor) {
    // No children or unsupported
    case YICES_BOOL_CONSTANT:
    case YICES_ARITH_CONSTANT:
    case YICES_BV_CONSTANT:
    case YICES_SCALAR_CONSTANT:
    case YICES_VARIABLE:
    case YICES_UNINTERPRETED_TERM:
    case YICES_SELECT_TERM:
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
      for (size_t i = 0; i < n; ++ i) {
        term_t child = yices_term_child(t, i);
        children.push_back(child);
      }
      break;
    }

    case YICES_BIT_TERM:
      children.push_back(yices_proj_arg(t));
      break;
    // sums
    case YICES_BV_SUM: {
      // sum a_i * t_i
      size_t bv_size = yices_term_bitsize(t);
      int32_t* a_i_bits = new int32_t[bv_size];
      size_t size = yices_term_num_children(t);
      for (size_t i = 0; i < size; ++i) {
        term_t t_i_yices;
        yices_bvsum_component(t, i, a_i_bits, &t_i_yices);
        if (t_i_yices != NULL_TERM) {
          children.push_back(t_i_yices);
        }
      }
      delete[] a_i_bits;
      break;
    }
    case YICES_ARITH_SUM: {
      mpq_t c_y;
      mpq_init(c_y);
      // sum c_i a_i
      size_t size = yices_term_num_children(t);
      for (size_t i = 0; i < size; ++ i) {
        term_t a_y;
        yices_sum_component(t, i, c_y, &a_y);
        if (a_y != NULL_TERM) {
          children.push_back(a_y);
        }
      }
      mpq_clear(c_y);
      break;
    }

    // products
    case YICES_POWER_PRODUCT: {
      size_t size = yices_term_num_children(t);
      for (size_t i = 0; i < size; ++ i) {
        term_t p_t;
        uint32_t p_d;
        yices_product_component(t, i, &p_t, &p_d);
        children.push_back(p_t);
      }
      break;
    }

    default:
      assert(false);
    }
  }

  // We visit all regular nodes
  // the cache yet
  expr::visitor_match_result match(term_t t) {
    // Anything already in the cache should not be visited
    if (!d_conversion_cache.get_term_cache(t).is_null()) {
      return expr::DONT_VISIT_AND_BREAK;
    }
    // Otherwise, visit any meaningful children
    return expr::VISIT_AND_CONTINUE;
  }

  void visit(term_t yices_term) {

    // All children visited already, so they exist in cache

    if (output::trace_tag_is_enabled("yices2::to_term")) {
      std::cerr << "to_term::visit: ";
      yices_pp_term(stderr, yices_term, 80, 100, 0);
    }

    expr::term_ref result;

    // Get the constructor type of t
    term_constructor_t t_constructor = yices_term_constructor(yices_term);

    switch (t_constructor) {
    // atomic terms
    case YICES_BOOL_CONSTANT: {
      int32_t value;
      yices_bool_const_value(yices_term, &value);
      result = d_tm.mk_boolean_constant(value);
      break;
    }
    case YICES_ARITH_CONSTANT: {
      mpq_t q;
      mpq_init(q);
      yices_rational_const_value(yices_term, q);
      expr::rational r(q);
      result = d_tm.mk_rational_constant(r);
      mpq_clear(q);
      break;
    }
    case YICES_BV_CONSTANT: {
      size_t size = yices_term_bitsize(yices_term);
      int32_t* bits = new int32_t[size];
      yices_bv_const_value(yices_term, bits);
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
      size_t n = yices_term_num_children(yices_term);
      std::vector<expr::term_ref> children;
      for (size_t i = 0; i < n; ++ i) {
        term_t child = yices_term_child(yices_term, i);
        expr::term_ref child_term = d_conversion_cache.get_term_cache(child);
        children.push_back(child_term);
      }
      result = d_yices.mk_term(t_constructor, children);
      break;
    }

    // projections
    case YICES_SELECT_TERM:
      assert(false);
      break;
    case YICES_BIT_TERM: {
      // Selects a bit, and the result is Boolean
      size_t index = yices_proj_index(yices_term);
      expr::term_ref argument = d_conversion_cache.get_term_cache(yices_proj_arg(yices_term));
      result = d_tm.mk_bitvector_extract(argument, expr::bitvector_extract(index, index));
      // Convert to boolean
      result = d_tm.mk_term(expr::TERM_EQ, result, d_bv1);
      break;
    }
    // sums
    case YICES_BV_SUM: {
      // sum a_i * t_i
      size_t bv_size = yices_term_bitsize(yices_term);
      int32_t* a_i_bits = new int32_t[bv_size];
      size_t size = yices_term_num_children(yices_term);
      std::vector<expr::term_ref> sum_children;
      for (size_t i = 0; i < size; ++i) {
        term_t t_i_yices;
        yices_bvsum_component(yices_term, i, a_i_bits, &t_i_yices);
        expr::term_ref a_i = d_tm.mk_bitvector_constant(yices_bv_to_bitvector(bv_size, a_i_bits));
        if (t_i_yices != NULL_TERM) {
          expr::term_ref t_i = d_conversion_cache.get_term_cache(t_i_yices);
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
      size_t size = yices_term_num_children(yices_term);
      std::vector<expr::term_ref> sum_children;
      for (size_t i = 0; i < size; ++ i) {
        term_t a_y;
        yices_sum_component(yices_term, i, c_y, &a_y);
        expr::term_ref c = d_tm.mk_rational_constant(expr::rational(c_y));
        if (a_y != NULL_TERM) {
          expr::term_ref a = d_conversion_cache.get_term_cache(a_y);
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
    case YICES_POWER_PRODUCT: {
      size_t size = yices_term_num_children(yices_term);
      std::vector<expr::term_ref> pow_children;
      for (size_t i = 0; i < size; ++ i) {
        term_t p_t;
        uint32_t p_d;
        yices_product_component(yices_term, i, &p_t, &p_d);
        while (p_d --) {
          pow_children.push_back(d_conversion_cache.get_term_cache(p_t));
        }
      }
      result = d_tm.mk_term(expr::TERM_BV_MUL, pow_children);
      break;
    }
    default:
      assert(false);
    }

    // At this point we need to be non-null
    if (result.is_null()) {
      std::stringstream ss;
      ss << "Yices error (term creation): " << yices2_internal::yices_error();
      throw exception(ss.str());
    }

    // Set the cache ref -> result
    d_conversion_cache.set_term_cache(yices_term, result);
  }
};


expr::term_ref yices2_internal::to_term(term_t yices_term) {
  to_term_visitor visitor(d_tm, *this, *d_conversion_cache);
  expr::term_visit_topological<to_term_visitor, term_t> visit_topological(visitor);
  visit_topological.run(yices_term);
  expr::term_ref result = d_conversion_cache->get_term_cache(yices_term);
  assert(!result.is_null());
  return result;
}

void yices2_internal::add(expr::term_ref ref, solver::formula_class f_class) {
  int ret_dpllt = 0;
  int ret_mcsat = 0;

  // Remember the assertions
  expr::term_ref_strong ref_strong(d_tm, ref);
  d_assertions.push_back(ref_strong);
  d_assertion_classes.push_back(f_class);

  // Assert to yices
  term_t yices_term = to_yices2_term(ref);
  if (output::trace_tag_is_enabled("yices2")) {
    yices_pp_term(stderr, yices_term, 80, 100, 0);
  }

  if (d_ctx_dpllt) {
    ret_dpllt = yices_assert_formula(d_ctx_dpllt, yices_term);
    if (ret_dpllt < 0) {
      error_code_t error = yices_error_code();
      if (error == CTX_NONLINEAR_ARITH_NOT_SUPPORTED) {
        // Unsupported -> incomplete
        yices_clear_error();
        d_dpllt_incomplete = true;
      } else {
        check_error(ret_dpllt, "Yices error (add)");
      }
    }
  }
  if (d_ctx_mcsat) {
    ret_mcsat = yices_assert_formula(d_ctx_mcsat, yices_term);
    if (ret_mcsat < 0) {
      error_code_t error = yices_error_code();
      if (error == MCSAT_ERROR_UNSUPPORTED_THEORY) {
        // Unsupported -> incomplete
        yices_clear_error();
        d_mcsat_incomplete = true;
      } else {
        check_error(ret_mcsat, "Yices error (add)");
      }
    }
  }
}

solver::result yices2_internal::check() {

  smt_status_t result;

  // Call DPLL(T) first, then MCSAT if unsupported
  if (d_ctx_dpllt) {
    result = d_last_check_status_dpllt = yices_check_context(d_ctx_dpllt, 0);
    d_last_check_status_mcsat = STATUS_UNKNOWN;
    switch (result) {
    case STATUS_SAT:
      if (!d_dpllt_incomplete) {
        return solver::SAT;
      } else {
        d_last_check_status_dpllt = STATUS_UNKNOWN;
        break; // Do MCSAT
      }
    case STATUS_UNSAT:
      return solver::UNSAT;
    case STATUS_UNKNOWN:
      break; // Do MCSAT
    default: {
      std::stringstream ss;
      ss << "Yices error (check): " << yices_error();
      throw exception(ss.str());
    }
    }
  }
  if (d_ctx_mcsat) {
    result = d_last_check_status_mcsat = yices_check_context(d_ctx_mcsat, 0);
    switch (result) {
    case STATUS_SAT:
      if (!d_mcsat_incomplete) {
        return solver::SAT;
      } else {
        d_last_check_status_mcsat = STATUS_UNKNOWN;
        break; // Nobody knows
      }
    case STATUS_UNSAT:
      return solver::UNSAT;
    case STATUS_UNKNOWN:
      return solver::UNKNOWN;
    default: {
      std::stringstream ss;
      ss << "Yices error (check): " << yices_error();
      throw exception(ss.str());
    }
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

model_t* yices2_internal::get_yices_model(expr::model::ref m) {

  // Get the variables
  std::vector<expr::term_ref> variables;
  bool class_A_used = false;
  bool class_B_used = false;
  bool class_T_used = false;
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
      class_T_used = true;
      break;
    default:
      assert(false);
    }
  }

  if (class_A_used) {
    variables.insert(variables.end(), d_A_variables.begin(), d_A_variables.end());
  }
  if (class_B_used) {
    variables.insert(variables.end(), d_B_variables.begin(), d_B_variables.end());
  }
  if (class_T_used) {
    variables.insert(variables.end(), d_T_variables.begin(), d_T_variables.end());
  }

  uint32_t n = variables.size();
  term_t* yices_variables = (term_t*) malloc(sizeof(term_t)*n);
  term_t* yices_values = (term_t*) malloc(sizeof(term_t)*n);

  size_t i;
  for (i = 0; i < variables.size(); ++ i) {
    yices_variables[i] = to_yices2_term(variables[i]);
    expr::value value = m->get_variable_value(variables[i]);
    if (value.is_bool()) {
      // Boolean value
      yices_values[i] = value.get_bool() ? yices_true() : yices_false();
    } else if (value.is_rational()) {
      // Rational value
      yices_values[i] = yices_mpq(value.get_rational().mpq().get_mpq_t());
    } else if (value.is_bitvector()) {
      // Bit-vector value
      yices_values[i] = yices_bvconst_mpz(value.get_bitvector().size(), value.get_bitvector().mpz().get_mpz_t());
    } else {
      assert(false);
    }
  }

  model_t* yices_model = yices_model_from_map(n, yices_variables, yices_values);

  free(yices_variables);
  free(yices_values);

  return yices_model;
}



expr::model::ref yices2_internal::get_model() {
  assert(d_last_check_status_dpllt == STATUS_SAT || d_last_check_status_mcsat == STATUS_SAT);
  assert(d_A_variables.size() > 0 || d_B_variables.size() > 0);

  int32_t ret = 0;

  // Clear any data already there
  expr::model::ref m = new expr::model(d_tm, false);

  // Get the model from yices
  model_t* yices_model =  (d_last_check_status_dpllt == STATUS_SAT) ?
      yices_get_model(d_ctx_dpllt, true) :
      yices_get_model(d_ctx_mcsat, true) ;

  if (output::trace_tag_is_enabled("yices2::model")) {
    yices_pp_model(stderr, yices_model, 80, 100000, 0);
  }

  // Get the variables
  std::vector<expr::term_ref> variables;
  bool class_A_used = false;
  bool class_B_used = false;
  bool class_T_used = false;
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
      class_T_used = true;
      break;
    default:
      assert(false);
    }
  }

  if (class_A_used) {
    variables.insert(variables.end(), d_A_variables.begin(), d_A_variables.end());
  }
  if (class_B_used) {
    variables.insert(variables.end(), d_B_variables.begin(), d_B_variables.end());
  }
  if (class_T_used) {
    variables.insert(variables.end(), d_T_variables.begin(), d_T_variables.end());
  }

  // See which variables we have to reason about
  for (size_t i = 0; i < variables.size(); ++ i) {
    expr::term_ref var = variables[i];
    term_t yices_var = to_yices2_term(var);
    expr::term_ref var_type = d_tm.type_of(var);

    expr::value var_value;
    switch (d_tm.term_of(var_type).op()) {
    case expr::TYPE_BOOL: {
      int32_t value;
      ret = yices_get_bool_value(yices_model, yices_var, &value);
      check_error(ret, "Error obtaining Bool value from Yices2 model.");
      var_value = expr::value(value);
      break;
    }
    case expr::TYPE_INTEGER: {
      // The integer mpz_t value
      mpz_t value;
      mpz_init(value);
      ret = yices_get_mpz_value(yices_model, yices_var, value);
      check_error(ret, "Error obtaining integer value from Yices2 model.");
      expr::rational rational_value(value);
      var_value = expr::value(rational_value);
      // Clear the temps
      mpz_clear(value);
      break;
    }
    case expr::TYPE_REAL: {
      // The integer mpz_t value
      mpq_t value;
      mpq_init(value);
      ret = yices_get_mpq_value(yices_model, yices_var, value);
      // rational
      if (ret == 0) {
        expr::rational rational_value(value);
        var_value = expr::value(rational_value);
      } else {
#ifdef WITH_LIBPOLY
        lp_algebraic_number_t a;
        lp_algebraic_number_construct_zero(&a);
        ret = yices_get_algebraic_number_value(yices_model, yices_var, &a);
        if (ret < 0) {
          throw exception("Error obtaining real value from Yices2 model.");
        }
        // TODO: proper algebraic numbers
        lp_rational_t a_q;
        lp_rational_construct(&a_q);
        lp_algebraic_number_to_rational(&a, &a_q);
        var_value = expr::rational(&a_q);
        lp_algebraic_number_destruct(&a);
        lp_rational_destruct(&a_q);
#else
        throw exception("Error obtaining real value from Yices2 model.");
#endif
      }
      // Clear the temps
      mpq_clear(value);
      break;
    }
    case expr::TYPE_BITVECTOR: {
      size_t size = d_tm.get_bitvector_type_size(var_type);
      int32_t* value = new int32_t[size];
      ret = yices_get_bv_value(yices_model, yices_var, value);
      check_error(ret, "Error obtaining bit-vector value from Yices2 model.");
      expr::bitvector bv = bitvector_from_int32(size, value);
      var_value = expr::value(bv);
      delete[] value;
      break;
    }
    default:
      assert(false);
    }

    // Add the association
    m->set_variable_value(var, var_value);
  }

  // Free the yices model
  yices_free_model(yices_model);

  return m;
}

void yices2_internal::push() {
  int ret = 0;
  if (d_ctx_dpllt) {
    ret = yices_push(d_ctx_dpllt);
    check_error(ret, "Yices error (push)");
  }
  if (d_ctx_mcsat) {
    ret = yices_push(d_ctx_mcsat);
    check_error(ret, "Yices error (push)");
  }
  d_assertions_size.push_back(d_assertions.size());
  d_dpllt_incomplete_log.push_back(d_dpllt_incomplete);
  d_mcsat_incomplete_log.push_back(d_mcsat_incomplete);
}

void yices2_internal::pop() {
  int ret = 0;
  if (d_ctx_dpllt) {
    ret = yices_pop(d_ctx_dpllt);
    check_error(ret, "Yices error (pop)");
  }
  if (d_ctx_mcsat) {
    ret = yices_pop(d_ctx_mcsat);
    check_error(ret, "Yices error (pop)");
  }
  size_t size = d_assertions_size.back();
  d_assertions_size.pop_back();
  while (d_assertions.size() > size) {
    d_assertions.pop_back();
    d_assertion_classes.pop_back();
  }
  d_dpllt_incomplete = d_dpllt_incomplete_log.back();
  d_dpllt_incomplete_log.pop_back();
  d_mcsat_incomplete = d_mcsat_incomplete_log.back();
  d_mcsat_incomplete_log.pop_back();
}

void yices2_internal::generalize(smt::solver::generalization_type type, std::vector<expr::term_ref>& projection_out) {

  assert(!d_assertions.empty());

  // Get the model
  expr::model::ref m = get_model();

  if (output::trace_tag_is_enabled("yices2")) {
    std::cerr << "model:" << (*m) << std::endl;
  }

  // Generalize with the current model
  generalize(type, m, projection_out);
}

void yices2_internal::generalize(smt::solver::generalization_type type, expr::model::ref m, std::vector<expr::term_ref>& projection_out) {

  assert(!d_assertions.empty());

  // When we generalize backward we eliminate from T and B
  // When we generalize forward we eliminate from A and T

  // Count the A/B formulas
  size_t assertions_size = 0;
  for (size_t i = 0; i < d_assertions.size(); ++ i) {
    switch (type) {
    case smt::solver::GENERALIZE_BACKWARD:
      if (d_assertion_classes[i] != solver::CLASS_A) {
        assertions_size++;
      }
      break;
    case smt::solver::GENERALIZE_FORWARD:
      if (d_assertion_classes[i] != solver::CLASS_B) {
        assertions_size++;
      }
      break;
    default:
      assert(false);
    }
  }

  // Yices version of the assertions for A/B
  term_t* assertions = new term_t[assertions_size];
  size_t j = 0;
  switch (type) {
  case smt::solver::GENERALIZE_BACKWARD:
    for (size_t i = 0; i < d_assertions.size(); ++ i) {
      if (d_assertion_classes[i] != solver::CLASS_A) {
        assertions[j++] = to_yices2_term(d_assertions[i]);
      }
    }
    break;
  case smt::solver::GENERALIZE_FORWARD:
    for (size_t i = 0; i < d_assertions.size(); ++ i) {
      if (d_assertion_classes[i] != solver::CLASS_B) {
        assertions[j++] = to_yices2_term(d_assertions[i]);
      }
    }
    break;
  default:
    assert(false);
  }

  // Yices version of the variables to eliminate
  size_t variables_size = type == smt::solver::GENERALIZE_BACKWARD ?
      d_B_variables.size() + d_T_variables.size() :
      d_A_variables.size() + d_T_variables.size() ;
  term_t* variables = new term_t[variables_size];

  j = 0;
  for (size_t i = 0; i < d_T_variables.size(); ++ i) {
    variables[j++] = to_yices2_term(d_T_variables[i]);
  }
  switch (type) {
  case smt::solver::GENERALIZE_BACKWARD:
    for (size_t i = 0; i < d_B_variables.size(); ++ i) {
      variables[j++] = to_yices2_term(d_B_variables[i]);
    }
    break;
  case smt::solver::GENERALIZE_FORWARD:
    for (size_t i = 0; i < d_A_variables.size(); ++ i) {
      variables[j++] = to_yices2_term(d_A_variables[i]);
    }
    break;
  }

  // Get yices model from model
  model_t* yices_model = get_yices_model(m);

  if (output::trace_tag_is_enabled("yices2::gen")) {
    std::cerr << "assertions:" << std::endl;
    for (size_t i = 0; i < assertions_size; ++ i) {
      std::cerr << i << ": ";
      yices_pp_term(stderr, assertions[i], 80, 100, 0);
    }
    std::cerr << "variables:" << std::endl;
    for (size_t i = 0; i < variables_size; ++ i) {
      std::cerr << i << ": ";
      yices_pp_term(stderr, variables[i], 80, 100, 0);
    }
    std::cerr << "model: ";
    yices_pp_model(stderr, yices_model, 80, 100, 0);
  }

  // Generalize
  term_vector_t G_y;
  yices_init_term_vector(&G_y);
  int32_t ret = yices_generalize_model_array(yices_model, assertions_size, assertions, variables_size, variables, YICES_GEN_DEFAULT, &G_y);
  if (ret < 0) {
    std::stringstream ss;
    ss << "Yices error (generalization): " << yices_error();
    throw exception(ss.str());
  }

  for (size_t i = 0; i < G_y.size; ++ i) {
    assert(yices_formula_true_in_model(yices_model, G_y.data[i]));
    expr::term_ref t_i = to_term(G_y.data[i]);
    projection_out.push_back(t_i);
  }

  // Check generalizatations
  if (output::trace_tag_is_enabled("yices2::check-generalization")) {
    static size_t id = 0;

    // we have
    //  \forall x G(x) => \exists y F(x, y) is valid
    //  \exists x G(x) and \forall y not F(x, y) is unsat

    // File to write to
    std::stringstream ss;
    ss << "gen_check_" << (id ++) << ".smt2";
    std::ofstream out(ss.str().c_str());
    efsmt_to_stream(out, &G_y, assertions, assertions_size, d_A_variables, d_T_variables, d_B_variables);
  }

  if (output::trace_tag_is_enabled("yices2::gen")) {
    std::cerr << "generalization: " << std::endl;
    for (size_t i = 0; i < projection_out.size(); ++ i) {
      std::cerr << i << ": "; yices_pp_term(stderr, G_y.data[i], 80, 100, 0);
      std::cerr << i << ": " << projection_out[i] << std::endl;
    }
  }

  yices_delete_term_vector(&G_y);

  // Free temps
  delete[] variables;
  delete[] assertions;
  yices_free_model(yices_model);
}

void yices2_internal::gc() {
  d_conversion_cache->gc();
}

void yices2_internal::get_assertions(std::set<expr::term_ref>& out) const {
  for (size_t i = 0; i < d_assertions.size(); ++ i) {
    out.insert(d_assertions[i]);
  }
}

void yices2_internal::add_variable(expr::term_ref var, smt::solver::variable_class f_class) {

  switch (f_class) {
  case smt::solver::CLASS_A:
    assert(d_A_variables_set.find(var) == d_A_variables_set.end());
    break;
  case smt::solver::CLASS_B:
    assert(d_B_variables_set.find(var) == d_B_variables_set.end());
    break;
  case smt::solver::CLASS_T:
    assert(d_T_variables_set.find(var) == d_T_variables_set.end());
    break;
  default:
    assert(false);
  }

  // Convert to yices2 early
  to_yices2_term(var);

  switch (f_class) {
  case smt::solver::CLASS_A:
    d_A_variables.push_back(var);
    d_A_variables_set.insert(var);
    break;
  case smt::solver::CLASS_B:
    d_B_variables.push_back(var);
    d_B_variables_set.insert(var);
    break;
  case smt::solver::CLASS_T:
    d_T_variables.push_back(var);
    d_T_variables_set.insert(var);
    break;
  default:
    assert(false);
  }
}

void yices2_internal::gc_collect(const expr::gc_relocator& gc_reloc) {
  gc_reloc.reloc(d_assertions);
  gc_reloc.reloc(d_A_variables);
  gc_reloc.reloc(d_B_variables);
  gc_reloc.reloc(d_T_variables);
  gc_reloc.reloc(d_bv1);
  gc_reloc.reloc(d_bv0);
}

void yices2_internal::efsmt_to_stream(std::ostream& out, const term_vector_t* G_y, const term_t* assertions, size_t assertions_size,
    const std::vector<expr::term_ref>& exists_vars,
    const std::vector<expr::term_ref>& forall_vars_1,
    const std::vector<expr::term_ref>& forall_vars_2) {

  out << expr::set_tm(d_tm);

  out << "(set-logic LRA)" << std::endl;
  out << "(set-info :smt-lib-version 2.0)" << std::endl;
  out << "(set-info :status unsat)" << std::endl;
  out << std::endl;

  for (size_t i = 0; i < exists_vars.size(); ++ i) {
    expr::term_ref variable = exists_vars[i];
    out << "(declare-fun " << variable << " () " << d_tm.type_of(variable) << ")" << std::endl;
  }

  out << std::endl;

  for (size_t i = 0; i < G_y->size; ++ i) {
    expr::term_ref assertion = to_term(G_y->data[i]);
    out << ";; G[" << i << "]" << std::endl;
    out << "(assert " << assertion << ")" << std::endl;
  }

  out << std::endl;
  out << "(assert (forall (";
  for (size_t i = 0; i < forall_vars_1.size(); ++ i) {
    expr::term_ref variable = forall_vars_1[i];
    if (i) out << " ";
    out << "(";
    out << variable << " " << d_tm.type_of(variable);
    out << ")";
  }
  for (size_t i = 0; i < forall_vars_2.size(); ++ i) {
    expr::term_ref variable = forall_vars_2[i];
    out << " (";
    out << variable << " " << d_tm.type_of(variable);
    out << ")";
  }
  out << ")" << std::endl; // end forall variables
  out << "(not (and";
  for (size_t i = 0; i < assertions_size; ++ i) {
    expr::term_ref assertion = to_term(assertions[i]);
    out << std::endl << "  " << assertion;
  }
  out << "))" << std::endl; // end negation and and

  out << "))" << std::endl; // end forall

  out << std::endl;
  out << "(check-sat)" << std::endl;
}


}
}

#endif
