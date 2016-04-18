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

#ifdef WITH_Z3

#include "smt/z3/z3_internal.h"
#include "smt/z3/z3_term_cache.h"
#include "utils/trace.h"
#include "expr/gc_relocator.h"
#include "utils/output.h"

#include <iostream>
#include <fstream>

namespace sally {
namespace smt {

int z3_internal::s_instances = 0;

z3_internal::z3_internal(expr::term_manager& tm, const options& opts)
: d_tm(tm)
, d_ctx(0)
, d_solver(0)
, d_conversion_cache(0)
, d_last_check_status(Z3_L_UNDEF)
, d_instance(s_instances)
{
  // Initialize
  if (s_instances == 0) {
    TRACE("z3") << "z3: first instance." << std::endl;
  }
  s_instances ++;
  d_conversion_cache = z3_term_cache::get_cache(tm);

  /** Set the context */
  d_ctx = d_conversion_cache->get_context();

  /** Make the solver */
  d_solver = Z3_mk_solver(d_ctx);
  Z3_solver_inc_ref(d_ctx, d_solver);

  // Bitvector bits
  d_bv0 = expr::term_ref_strong(d_tm, d_tm.mk_bitvector_constant(expr::bitvector(1, 0)));
  d_bv1 = expr::term_ref_strong(d_tm, d_tm.mk_bitvector_constant(expr::bitvector(1, 1)));
}

z3_internal::~z3_internal() {

  // The context
  Z3_solver_dec_ref(d_ctx, d_solver);

  // Cleanup if the last one
  s_instances--;
  if (s_instances == 0) {
    TRACE("z3") << "z3: last instance removed." << std::endl;
    // Clear the cache
    d_conversion_cache->clear();
  }
}

Z3_ast z3_internal::mk_z3_term(expr::term_op op, size_t n, const std::vector<Z3_ast>& children_vec) {

  Z3_ast result;
  const Z3_ast* children = &children_vec[0];

  switch (op) {
  case expr::TERM_AND:
    result = Z3_mk_and(d_ctx, n, children);
    break;
  case expr::TERM_OR:
    result = Z3_mk_or(d_ctx, n, children);
    break;
  case expr::TERM_NOT:
    assert(n == 1);
    result = Z3_mk_not(d_ctx, children[0]);
    break;
  case expr::TERM_IMPLIES:
    assert(n == 2);
    result = Z3_mk_implies(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_XOR:
    assert(n == 2);
    result = Z3_mk_xor(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_ADD:
    result = Z3_mk_add(d_ctx, n, children);
    break;
  case expr::TERM_SUB:
    assert(n == 2 || n == 1);
    if (n == 1) {
      result = Z3_mk_unary_minus(d_ctx, children[0]);
    } else {
      result = Z3_mk_sub(d_ctx, 2, children);
    }
    break;
  case expr::TERM_MUL:
    result = Z3_mk_mul(d_ctx, n, children);
    break;
  case expr::TERM_DIV:
    assert(n == 2);
    result = Z3_mk_div(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_LEQ:
    assert(n == 2);
    result = Z3_mk_le(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_LT:
    assert(n == 2);
    result = Z3_mk_lt(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_GEQ:
    assert(n == 2);
    result = Z3_mk_ge(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_GT:
    assert(n == 2);
    result = Z3_mk_gt(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_EQ:
    assert(n == 2);
    result = Z3_mk_eq(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_ITE:
    assert(n == 3);
    result = Z3_mk_ite(d_ctx, children[0], children[1], children[2]);
    break;
  case expr::TERM_BV_ADD:
    assert(n == 2);
    result = Z3_mk_bvadd(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_SUB:
    if (n == 1) {
      result = Z3_mk_bvneg(d_ctx, children[0]);
    } else {
      result = Z3_mk_bvsub(d_ctx, children[0], children[1]);
    }
    break;
  case expr::TERM_BV_MUL:
    assert(n == 2);
    result = Z3_mk_bvmul(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_UDIV: // NOTE: semantics of division is x/0 = 111...111
    assert(n == 2);
    result = Z3_mk_bvudiv(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_SDIV:
    assert(n == 2);
    result = Z3_mk_bvsdiv(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_UREM:
    assert(n == 2);
    result = Z3_mk_bvurem(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_SREM:
    assert(n == 2);
    result = Z3_mk_bvsrem(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_SMOD:
    assert(n == 2);
    result = Z3_mk_bvsmod(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_XOR:
    assert(n == 2);
    result = Z3_mk_bvxor(d_ctx, children[0], children[2]);
    break;
  case expr::TERM_BV_SHL:
    assert(n == 2);
    result = Z3_mk_bvshl(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_LSHR:
    assert(n == 2);
    result = Z3_mk_bvlshr(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_ASHR:
    assert(n == 2);
    result = Z3_mk_bvashr(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_NOT:
    assert(n == 1);
    result = Z3_mk_bvnot(d_ctx, children[0]);
    break;
  case expr::TERM_BV_AND:
    assert(n == 2);
    result = Z3_mk_bvand(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_OR:
    assert(n == 2);
    result = Z3_mk_bvor(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_NAND:
    assert(n == 2);
    result = Z3_mk_bvnand(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_NOR:
    assert(n == 2);
    result = Z3_mk_bvnor(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_XNOR:
    assert(n == 2);
    result = Z3_mk_bvxnor(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_CONCAT:
    assert(n == 2);
    result = Z3_mk_concat(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_ULEQ:
    assert(n == 2);
    result = Z3_mk_bvule(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_SLEQ:
    assert(n == 2);
    result = Z3_mk_bvsle(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_ULT:
    assert(n == 2);
    result = Z3_mk_bvult(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_SLT:
    assert(n == 2);
    result = Z3_mk_bvslt(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_UGEQ:
    assert(n == 2);
    result = Z3_mk_bvuge(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_SGEQ:
    assert(n == 2);
    result = Z3_mk_bvsge(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_UGT:
    assert(n == 2);
    result = Z3_mk_bvugt(d_ctx, children[0], children[1]);
    break;
  case expr::TERM_BV_SGT:
    assert(n == 2);
    result = Z3_mk_bvsgt(d_ctx, children[0], children[1]);
    break;
  default:
    assert(false);
  }

  Z3_error_code error = Z3_get_error_code(d_ctx);
  if (error != Z3_OK) {
    std::stringstream ss;
    Z3_string msg = Z3_get_error_msg(d_ctx, error);
    ss << "Z3 error (term creation): " << msg << " for op " << op << " and terms";
    for (size_t i = 0; i < n; ++ i) {
      Z3_string term_rep = Z3_ast_to_string(d_ctx, children[i]);
      if (i) { ss << ", "; }
      else { ss << " "; }
      ss << term_rep;
    }
    throw exception(ss.str());
  }

  return result;
}

Z3_sort z3_internal::to_z3_type(expr::term_ref ref) {

  Z3_sort result;

  switch (d_tm.term_of(ref).op()) {
  case expr::TYPE_BOOL:
    result = Z3_mk_bool_sort(d_ctx);
    break;
  case expr::TYPE_INTEGER:
    result = Z3_mk_int_sort(d_ctx);
    break;
  case expr::TYPE_REAL:
    result = Z3_mk_real_sort(d_ctx);
    break;
  case expr::TYPE_BITVECTOR: {
    size_t size = d_tm.get_bitvector_type_size(ref);
    result = Z3_mk_bv_sort(d_ctx, size);
    break;
  }
  default:
    assert(false);
  }

  Z3_error_code error = Z3_get_error_code(d_ctx);
  if (error != Z3_OK) {
    std::stringstream ss;
    Z3_string msg = Z3_get_error_msg(d_ctx, error);
    ss << "Z3 error (term creation): " << msg << " for term " << ref;
    throw exception(ss.str());
  }

  return result;
}

Z3_ast z3_internal::to_z3_term(expr::term_ref ref) {

  Z3_ast result;

  // Check the term has been translated already
  result = d_conversion_cache->get_term_cache(ref);
  if (result != 0) {
    return result;
  }

  // The term
  const expr::term& t = d_tm.term_of(ref);
  expr::term_op t_op = t.op();

  // Temps to decref after we're done
  std::vector<Z3_ast> to_decref;

  switch (t_op) {
  case expr::VARIABLE: {
    Z3_symbol symbol = Z3_mk_string_symbol(d_ctx, d_tm.get_variable_name(t).c_str());
    Z3_sort sort = to_z3_type(t[0]);
    Z3_inc_ref(d_ctx, Z3_sort_to_ast(d_ctx, sort));
    to_decref.push_back(Z3_sort_to_ast(d_ctx, sort));
    result = Z3_mk_const(d_ctx, symbol, sort);
    d_conversion_cache->set_term_cache(result, ref);
    break;
  }
  case expr::CONST_BOOL:
    result = d_tm.get_boolean_constant(t) ? Z3_mk_true(d_ctx) : Z3_mk_false(d_ctx);
    break;
  case expr::CONST_RATIONAL: {
    Z3_sort sort = Z3_mk_real_sort(d_ctx);
    Z3_inc_ref(d_ctx, Z3_sort_to_ast(d_ctx, sort));
    to_decref.push_back(Z3_sort_to_ast(d_ctx, sort));
    result = Z3_mk_numeral(d_ctx, d_tm.get_rational_constant(t).mpq().get_str(10).c_str(), sort);
    break;
  }
  case expr::CONST_BITVECTOR: {
    const expr::bitvector& bv = d_tm.get_bitvector_constant(t);
    Z3_sort bv_sort = Z3_mk_bv_sort(d_ctx, bv.size());
    Z3_inc_ref(d_ctx, Z3_sort_to_ast(d_ctx, bv_sort));
    to_decref.push_back(Z3_sort_to_ast(d_ctx, bv_sort));
    result = Z3_mk_numeral(d_ctx, bv.mpz().get_str(10).c_str(), bv_sort);
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
    std::vector<Z3_ast> children;
    for (size_t i = 0; i < size; ++ i) {
      children.push_back(to_z3_term(t[i]));
    }
    result = mk_z3_term(t.op(), size, children);
    break;
  }
  case expr::TERM_BV_EXTRACT: {
    const expr::bitvector_extract& extract = d_tm.get_bitvector_extract(t);
    Z3_ast child = to_z3_term(t[0]);
    result = Z3_mk_extract(d_ctx, extract.high, extract.low, child);
    break;
  }
  default:
    assert(false);
  }

  Z3_error_code error = Z3_get_error_code(d_ctx);
  if (error != Z3_OK) {
    std::stringstream ss;
    Z3_string msg = Z3_get_error_msg(d_ctx, error);
    ss << "Z3 error (term creation): " << msg << " for term " << ref;
    throw exception(ss.str());
  }

  // Set the cache ref -> result
  d_conversion_cache->set_term_cache(ref, result);

  for (size_t i = 0; i < to_decref.size(); ++ i) {
    Z3_dec_ref(d_ctx, to_decref[i]);
  }

  return result;
}

expr::term_ref z3_internal::to_term(Z3_ast z3_term) {

  expr::term_ref result;

  // Check the cache
  result = d_conversion_cache->get_term_cache(z3_term);
  if (!result.is_null()) {
    return result;
  }

  // Get the constructor type of t
  Z3_ast_kind t_kind = Z3_get_ast_kind(d_ctx, z3_term);

  switch (t_kind) {
  case Z3_NUMERAL_AST:
    break;
  case Z3_APP_AST:
    break;
  case Z3_VAR_AST:
    break;
  case Z3_QUANTIFIER_AST:
    assert(false);
    break;
  case Z3_SORT_AST:
    assert(false);
    break;
  case Z3_FUNC_DECL_AST:
    break;
  default:
    assert(false);
  }

  if (result.is_null()) {
    std::stringstream ss;
    ss << "Error converting z3 term ";
    Z3_string term_ref = Z3_ast_to_string(d_ctx, z3_term);
    ss << term_ref;
    throw exception(ss.str());
  }

  // Set the cache ref -> result
  d_conversion_cache->set_term_cache(z3_term, result);

  return result;
}

void z3_internal::add(expr::term_ref ref, solver::formula_class f_class) {
  // Remember the assertions
  expr::term_ref_strong ref_strong(d_tm, ref);
  d_assertions.push_back(ref_strong);
  d_assertion_classes.push_back(f_class);

  // Assert to yices
  Z3_ast z3_term = to_z3_term(ref);
  Z3_solver_assert(d_ctx, d_solver, z3_term);

  Z3_error_code error = Z3_get_error_code(d_ctx);
  if (error != Z3_OK) {
    std::stringstream ss;
    Z3_string msg = Z3_get_error_msg(d_ctx, error);
    ss << "Z3 error (add): " << msg << " for assertion " << ref;
    throw exception(ss.str());
  }
}

solver::result z3_internal::check() {
  d_last_check_status = Z3_solver_check(d_ctx, d_solver);

  switch (d_last_check_status) {
  case Z3_L_FALSE:
    return solver::UNSAT;
  case Z3_L_UNDEF:
    return solver::UNKNOWN;
  case Z3_L_TRUE:
    return solver::SAT;
  default:
    assert(false);
  }

  return solver::UNKNOWN;
}

expr::model::ref z3_internal::get_model(const std::set<expr::term_ref>& x_variables, const std::set<expr::term_ref>& T_variables, const std::set<expr::term_ref>& y_variables) {
  assert(d_last_check_status == Z3_L_TRUE);
  assert(x_variables.size() > 0 || y_variables.size() > 0);

  // Clear any data already there
  expr::model::ref m = new expr::model(d_tm, false);

  // Get the model from z3
  Z3_model z3_model = Z3_solver_get_model(d_ctx, d_solver);
  Z3_error_code error = Z3_get_error_code(d_ctx);
  if (error != Z3_OK) {
    std::stringstream ss;
    Z3_string msg = Z3_get_error_msg(d_ctx, error);
    ss << "Z3 error (model): " << msg << ".";
    throw exception(ss.str());
  }
  Z3_model_inc_ref(d_ctx, z3_model);

  if (output::trace_tag_is_enabled("z3::model")) {
    std::cerr << Z3_model_to_string(d_ctx, z3_model) << std::endl;
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
    variables.insert(variables.end(), x_variables.begin(), x_variables.end());
  }
  if (class_B_used) {
    variables.insert(variables.end(), y_variables.begin(), y_variables.end());
  }
  if (class_T_used) {
    variables.insert(variables.end(), T_variables.begin(), T_variables.end());
  }

  // See which variables we have to reason about
  for (size_t i = 0; i < variables.size(); ++ i) {
    expr::term_ref var = variables[i];
    Z3_ast z3_var = to_z3_term(var);
    expr::term_ref var_type = d_tm.type_of(var);
    Z3_ast value;
    bool ok = Z3_model_eval(d_ctx, z3_model, z3_var, 1, &value);
    if (ok) {
      Z3_inc_ref(d_ctx, value);
    }

    expr::value var_value;
    switch (d_tm.term_of(var_type).op()) {
    case expr::TYPE_BOOL: {
      var_value = expr::value(Z3_get_bool_value(d_ctx, value));
      break;
    }
    case expr::TYPE_INTEGER: {
      Z3_string value_string = Z3_get_numeral_string(d_ctx, value);
      expr::rational q_value(value_string);
      var_value = expr::value(q_value);
      break;
    }
    case expr::TYPE_REAL: {
      Z3_string value_string = Z3_get_numeral_string(d_ctx, value);
      expr::rational q_value(value_string);
      var_value = expr::value(q_value);
      break;
    }
    case expr::TYPE_BITVECTOR: {
      Z3_string value_string = Z3_get_numeral_string(d_ctx, value);
      size_t bv_size = d_tm.get_bitvector_size(var);
      expr::integer z_value(value_string, 10);
      var_value = expr::value(expr::bitvector(bv_size, z_value));
      break;
    }
    default:
      assert(false);
    }

    if (ok) {
      Z3_dec_ref(d_ctx, value);
    }

    // Add the association
    m->set_variable_value(var, var_value);

    Z3_error_code error = Z3_get_error_code(d_ctx);
    if (error != Z3_OK) {
      std::stringstream ss;
      Z3_string msg = Z3_get_error_msg(d_ctx, error);
      ss << "Z3 error (model): " << msg << ".";
      throw exception(ss.str());
    }
}

  // Free the yices model
  Z3_model_dec_ref(d_ctx, z3_model);

  return m;
}

void z3_internal::push() {
  Z3_solver_push(d_ctx, d_solver);
  Z3_error_code error = Z3_get_error_code(d_ctx);
  if (error != Z3_OK) {
    std::stringstream ss;
    Z3_string msg = Z3_get_error_msg(d_ctx, error);
    ss << "Z3 error (push): " << msg << ".";
    throw exception(ss.str());
  }
  d_assertions_size.push_back(d_assertions.size());
}

void z3_internal::pop() {
  Z3_solver_pop(d_ctx, d_solver, 1);
  Z3_error_code error = Z3_get_error_code(d_ctx);
  if (error != Z3_OK) {
    std::stringstream ss;
    Z3_string msg = Z3_get_error_msg(d_ctx, error);
    ss << "Z3 error (push): " << msg << ".";
    throw exception(ss.str());
  }
  size_t size = d_assertions_size.back();
  d_assertions_size.pop_back();
  while (d_assertions.size() > size) {
    d_assertions.pop_back();
    d_assertion_classes.pop_back();
  }
}

void z3_internal::gc() {
  d_conversion_cache->gc();
}

void z3_internal::get_assertions(std::set<expr::term_ref>& out) const {
  for (size_t i = 0; i < d_assertions.size(); ++ i) {
    out.insert(d_assertions[i]);
  }
}

void z3_internal::add_variable(expr::term_ref var, smt::solver::variable_class f_class) {

  // Convert to z3 early
  to_z3_term(var);

  switch (f_class) {
  case smt::solver::CLASS_A:
    d_A_variables.push_back(var);
    break;
  case smt::solver::CLASS_B:
    d_B_variables.push_back(var);
    break;
  case smt::solver::CLASS_T:
    d_T_variables.push_back(var);
    break;
  default:
    assert(false);
  }
}

void z3_internal::interpolate(std::vector<expr::term_ref>& out) {
  assert(false);
}

void z3_internal::gc_collect(const expr::gc_relocator& gc_reloc) {
  gc_reloc.reloc(d_assertions);
  gc_reloc.reloc(d_A_variables);
  gc_reloc.reloc(d_B_variables);
  gc_reloc.reloc(d_T_variables);
  gc_reloc.reloc(d_bv1);
  gc_reloc.reloc(d_bv0);
}

}
}

#endif
