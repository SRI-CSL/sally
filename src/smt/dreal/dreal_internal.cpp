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

#ifdef WITH_DREAL

#include "smt/dreal/dreal_internal.h"
#include "smt/dreal/dreal_term_cache.h"
#include "utils/trace.h"
#include "expr/gc_relocator.h"
#include "expr/term.h"
#include "expr/term_manager.h"
#include "expr/term_visitor.h"
#include "utils/output.h"

#ifdef WITH_LIBPOLY
#include "poly/rational.h"
#include "poly/interval.h"
#endif

#include <ibex.h>

#include <iostream>
#include <fstream>

using namespace dreal;

namespace sally {
namespace smt {

size_t dreal_internal::s_instances = 0;

dreal_internal::dreal_internal(expr::term_manager& tm, const options& opts)
: d_tm(tm)
, d_ctx(0)
, d_ctx_bounded(0)
, d_conversion_cache(0)
, d_last_check_status(solver::result::UNKNOWN)
, d_config(0)
, d_instance(s_instances)
, d_options(opts)
{
  // Initialize
  TRACE("dreal") << "dreal: created dreal[" << s_instances << "]." << std::endl;      

  s_instances++;
  d_conversion_cache = dreal_term_cache::get_cache(d_tm);

  // The config
  d_config = new Config();
  if (!d_config) {
    throw exception("Dreal error (config creation)");
  }

  // some basic options
  d_config->mutable_produce_models() = true;

  //default precision (only has default from command line)
  double prec = 0.0001;
  if (opts.has_option("dreal-precision")) {
    prec = opts.get_double("dreal-precision");
  }
  d_config->mutable_precision() = prec;

  if (opts.has_option("dreal-polytope")) {
    d_config->mutable_use_polytope() = true;
  }
  
  // The context
  d_ctx = new Context {*d_config};
  if (!d_ctx) {
    throw exception("Dreal error (context creation)");
  }
  if (d_options.has_option("dreal-bound")) {
    d_ctx_bounded = new Context {*d_config};
    if (!d_ctx_bounded) {
      throw exception("Dreal error (context creation)");
    }
  }
}

dreal_internal::~dreal_internal() {

  // The config
  if (d_config) {
    delete d_config;
  }

  // The context
  if (d_ctx) {
    d_ctx->Exit();
    delete d_ctx;
  }
  if (d_ctx_bounded) {
    d_ctx_bounded->Exit();
    delete d_ctx_bounded;
  }

  // Cleanup if the last one
  s_instances--;
  if (s_instances == 0) {
    // Clear the cache
    d_conversion_cache->clear();
  }
  TRACE("dreal") << "dreal: removed dreal[" << s_instances << "]." << std::endl;    
}

dreal_term dreal_internal::mk_dreal_term(expr::term_op op, std::vector<dreal_term>& children) {
  dreal_term result;
  size_t n = children.size();
  switch (op) {
  case expr::TERM_AND:
    result = dreal_term::dreal_and(children);
    break;
  case expr::TERM_OR:
    result = dreal_term::dreal_or(children);
    break;
  case expr::TERM_NOT:
    assert(n == 1);
    result = dreal_term::dreal_not(children[0]);
    break;
  case expr::TERM_IMPLIES:
    assert(n == 2);
    result = dreal_term::dreal_or(dreal_term::dreal_not(children[0]), children[1]);
    break;
  case expr::TERM_ADD:
    result = dreal_term::dreal_add(children);
    break;
  case expr::TERM_SUB:
    assert(n == 2 || n == 1);
    if (n == 1) {
      result = dreal_term::dreal_sub(children[0]);
    } else {
      result = dreal_term::dreal_sub(children[0], children[1]);
    }
    break;
  case expr::TERM_MUL:
    result = dreal_term::dreal_mul(children);
    break;
  case expr::TERM_DIV:
    result = dreal_term::dreal_div(children[0], children[1]);
    break;
  case expr::TERM_LEQ:
    assert(n == 2);
    result = dreal_term::dreal_leq(children[0], children[1]);
    break;
  case expr::TERM_LT:
    assert(n == 2);
    result = dreal_term::dreal_lt(children[0], children[1]);
    break;
  case expr::TERM_GEQ:
    assert(n == 2);
    result = dreal_term::dreal_geq(children[0], children[1]);
    break;
  case expr::TERM_GT:
    assert(n == 2);
    result = dreal_term::dreal_gt(children[0], children[1]);
    break;
  case expr::TERM_EQ:
    assert(n == 2);
    result = dreal_term::dreal_eq(children[0], children[1]);
    break;
  case expr::TERM_ITE:
    assert(n == 3);
    result = dreal_term::dreal_ite(children[0], children[1], children[2]);
    break;
  case expr::TERM_TO_REAL:
    assert(n == 1);
    result = children[0];
    break;
  case expr::TERM_XOR:
  default:
    assert(false);
  }

  if (result.is_null_term()) {
    std::stringstream ss;
    ss << "Dreal error (term creation) for op " << op << " and terms";
    for (size_t i = 0, e = children.size(); i < e; ++ i) {
      if (i) { ss << ", "; }
      else {ss << " "; }
      ss << children[i].to_string();
    }
    throw exception(ss.str());
  }

  return result;
}

Variable::Type dreal_internal::to_dreal_type(expr::term_ref ref) {
  expr::term_op op = d_tm.term_of(ref).op();
  switch (op) {
  case expr::TYPE_BOOL: return Variable::Type::BOOLEAN;
  case expr::TYPE_INTEGER: return Variable::Type::INTEGER;    
  case expr::TYPE_REAL: return Variable::Type::CONTINUOUS;    
  default: ;;
  }
  
  std::stringstream ss;
  ss << "Dreal error (term creation): unsupported type " << op;
  throw exception(ss.str());
}

class to_dreal_visitor {

  expr::term_manager& d_tm;
  dreal_internal& d_dreal;
  dreal_term_cache& d_conversion_cache;
  std::vector<dreal_term> d_extra_assertions;
  std::vector<dreal_term> d_extra_variables;

  bool d_subexpr_to_vars;

  bool convert_to_variable(const expr::term_op op, const std::vector<dreal_term>& children) {

    if (!d_subexpr_to_vars) {
      return false;
    }

    size_t constant_count = 0;
    for (size_t i = 0; i < children.size(); ++ i){
      if (!children[i].is_expression()) { continue; }
      if (::is_constant(children[i].expression())) { constant_count ++; }
      else if (::is_real_constant(children[i].expression())) { constant_count ++; }
    }

    switch (op) {
      case expr::TERM_MUL:
        // Linear mult don't simplify
        if (children.size() - constant_count == 1) {
          return false;
        }
        return true;
      default:
        return false;
    }
    return false;
  }

public:

  to_dreal_visitor(expr::term_manager& tm, dreal_internal& dreal,
                   dreal_term_cache& cache, bool subexpr_to_vars)
  : d_tm(tm)
  , d_dreal(dreal)
  , d_conversion_cache(cache)
  , d_subexpr_to_vars(subexpr_to_vars)
  {}

  // Non-null terms are good
  bool is_good_term(expr::term_ref t) const {
    return !t.is_null();
  }

  bool has_extra_assertions() const { return d_extra_assertions.size() > 0; }
  bool has_extra_variables() const { return d_extra_variables.size() > 0; }

  const std::vector<dreal_term>& get_extra_assertions() const { return d_extra_assertions; }
  const std::vector<dreal_term>& get_extra_variables() const { return d_extra_variables; }

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
    if (!d_conversion_cache.get_term_cache(t).is_null_term()) {
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
    dreal_term result;

    TRACE("dreal:to_dreal") << "convert::visit(" << ref << ")" << std::endl;

    // The term
    const expr::term& t = d_tm.term_of(ref);
    expr::term_op t_op = t.op();

    switch (t_op) {
    case expr::VARIABLE: {
      result = dreal_term(d_tm.get_variable_name(t), d_dreal.to_dreal_type(t[0]));
      break;
    }
    case expr::CONST_BOOL: {
      result = dreal_term(d_tm.get_boolean_constant(t));
      break;
    }
    case expr::CONST_RATIONAL: {
      // We parse rationals (/ a b) as division
      // TODO: Actual floating point constants should be convertible?
      double d = mpq_get_d(d_tm.get_rational_constant(t).mpq().get_mpq_t());
      result = dreal_term(d);
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
    {
      size_t size = t.size();
      assert(size > 0);
      std::vector<dreal_term> children;
      children.reserve(size);
      for (size_t i = 0; i < size; ++ i) {
        children.push_back(d_conversion_cache.get_term_cache(t[i]));
      }
      result = d_dreal.mk_dreal_term(t.op(), children);

      if (convert_to_variable(t.op(), children)) {
        static int tmp = 0;
        std::stringstream ss;
        ss << "__tmp" << (tmp ++);
        expr::term_ref type = d_tm.type_of(t);
        dreal_term tmp_var(ss.str(), d_dreal.to_dreal_type(type));
        dreal_term eq = dreal_term::dreal_eq(tmp_var, result);
        d_extra_variables.push_back(tmp_var);
        d_extra_assertions.push_back(eq);
        result = tmp_var;
      }

      break;
    }
    case expr::CONST_BITVECTOR:
    case expr::TERM_BV_ADD:
    case expr::TERM_BV_SUB:
    case expr::TERM_BV_MUL:
    case expr::TERM_BV_UDIV:
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
    case expr::TERM_BV_EXTRACT:
    default:
      assert(false);
    }

    if (result.is_null_term()) {
      std::stringstream ss;
      ss << "Dreal error (term creation): could not convert " << ref;
      throw exception(ss.str());
    }

    // Set the cache ref -> result
    d_conversion_cache.set_term_cache(ref, result);
  }
};

dreal_term dreal_internal::to_dreal_term(expr::term_ref ref) {
  to_dreal_visitor visitor(d_tm, *this, *d_conversion_cache, d_options.has_option("dreal-subexpr-to-vars"));
  expr::term_visit_topological<to_dreal_visitor, expr::term_ref, expr::term_ref_hasher>
    topological_visit(visitor);
  topological_visit.run(ref);
  dreal_term result = d_conversion_cache->get_term_cache(ref);
  assert(!result.is_null_term());

  if (visitor.has_extra_variables()) {
    const std::vector<dreal_term>& variables = visitor.get_extra_variables();
    for (size_t i = 0; i < variables.size(); ++ i) {
      dreal_term var = variables[i];
      d_ctx->DeclareVariable(var.variable(), false);
      if (d_ctx_bounded) {
        d_ctx_bounded->DeclareVariable(var.variable(), false);
      }
    }
  }

  if (visitor.has_extra_assertions()) {
    const std::vector<dreal_term>& assertions = visitor.get_extra_assertions();
    for (size_t i = 0; i < assertions.size(); ++ i) {
      dreal_term assertion = assertions[i];
      TRACE("dreal") << assertion.to_smtlib2() << std::endl;
      d_ctx->Assert(assertion.formula());
      if (d_ctx_bounded) {
        d_ctx_bounded->Assert(assertion.formula());
      }
    }
  }

  return result;
}

void dreal_internal::add(expr::term_ref ref, solver::formula_class f_class) {
  // Remember the assertions
  expr::term_ref_strong ref_strong(d_tm, ref);
  d_assertions.push_back(ref_strong);

  // Assert to dreal
  dreal_term dreal_t = to_dreal_term(ref);
  assert(dreal_t.is_formula());
  Formula f = dreal_t.formula();
  d_assertions_dreal.push_back(f);
  TRACE("dreal") << dreal_t.to_smtlib2() << std::endl;
  d_ctx->Assert(f);
  if (d_ctx_bounded) {
    d_ctx_bounded->Assert(f);
  }
  d_last_check_status = solver::UNKNOWN;
}

solver::result dreal_internal::check() {

  // Set bounds if needed
  if (d_ctx_bounded) {
    TRACE("dreal") << "dreal[" << instance() << "]: bounded check, precision = " << d_ctx_bounded->config().precision() << std::endl;
    auto res = d_ctx_bounded->CheckSat();
    // If we got a model check the result and use it
    if (res) {
      TRACE("dreal") << "dreal[" << instance() << "]: seems sat" << std::endl;
      if (save_dreal_model(*res)) {
         d_last_check_status = solver::SAT;
      } else {
        d_last_check_status = solver::UNKNOWN;
      }
      TRACE("dreal") << "dreal[" << instance() << "]: bounded check: " << d_last_check_status << std::endl;
      return d_last_check_status;
    } else {
      // Unsat we don't know because we added manual bounds, continue with
      // a regular check
      TRACE("dreal") << "dreal[" << instance() << "]: bounded check: " << d_last_check_status << std::endl;
    }
  }

  if (auto res = d_ctx->CheckSat()) {
    TRACE("dreal") << "dreal[" << instance() << "]: checking model" << std::endl;
    // If sat then dreal returns a mapping from a variable to an interval.
    // We return sat only if all intervals are singleton
    if (save_dreal_model(*res)) {
      d_last_check_status = solver::SAT;
    } else {
      d_last_check_status = solver::UNKNOWN;
    }
  } else {
    d_last_check_status = solver::UNSAT;    
  }

  return d_last_check_status;
}

bool dreal_internal::check_model() const {
  for (size_t i = 0; i < d_assertions.size(); ++ i) {
    expr::term_ref f = d_assertions[i];
    if (!d_last_model->is_true(f)) {
      return false;
    }
  }
  return true;
}

bool dreal_internal::save_dreal_model(const Box& model) {

  // Get the model for each variable
  term_to_rational_map simple_model;

  for (size_t i = 0; i < d_variables.size(); ++ i) {
    expr::term_ref var = d_variables[i];
    dreal_term dreal_var = to_dreal_term(var);
    assert(dreal_var.is_variable());

    const Variable &x = dreal_var.variable();
    expr::rational x_value;

    /*
     * BD: added this check to make sure x is defined in the dreal model
     * before we ask for its interval value. Otherwise, the query
     *   iv = model[x]
     * has bizarre side-effects on the dreal model and context.
     */
    if (model.has_variable(x)) {
      const ibex::Interval& iv = model[x];
#ifdef WITH_LIBPOLY
      double lb = iv.lb();
      double ub = iv.ub();

      expr::rational lb_rat(lb);
      expr::rational ub_rat(ub);
      assert(lb_rat <= ub_rat);
      bool strict = lb_rat < ub_rat;

      lp_value_t lb_lp;
      if (lb == NEG_INFINITY) {
        lp_value_construct(&lb_lp, LP_VALUE_MINUS_INFINITY, 0);
      } else {
        lp_value_construct(&lb_lp, LP_VALUE_RATIONAL, lb_rat.mpq().__get_mp());
      }

      lp_value_t ub_lp;
      if (ub == POS_INFINITY) {
        lp_value_construct(&ub_lp, LP_VALUE_PLUS_INFINITY, 0);
      } else {
        lp_value_construct(&ub_lp, LP_VALUE_RATIONAL, ub_rat.mpq().__get_mp());
      }

      lp_interval_t iv_lp;
      lp_interval_construct(&iv_lp, &lb_lp, strict, &ub_lp, strict);

      lp_value_t x_value_lp;
      lp_value_construct_none(&x_value_lp);
      lp_interval_pick_value(&iv_lp, &x_value_lp);

      lp_rational_t x_value_rational;
      switch (x_value_lp.type) {
      case LP_VALUE_DYADIC_RATIONAL:
        lp_rational_construct_from_dyadic(&x_value_rational, &x_value_lp.value.dy_q);
        break;
      case LP_VALUE_RATIONAL:
        lp_rational_construct_copy(&x_value_rational, &x_value_lp.value.q);
        break;
      case LP_VALUE_INTEGER:
        lp_rational_construct_from_integer(&x_value_rational, &x_value_lp.value.z);
        break;
      default:
        assert(false);
      }

      x_value = expr::rational(&x_value_rational);

      lp_rational_destruct(&x_value_rational);
      lp_interval_destruct(&iv_lp);
      lp_value_destruct(&x_value_lp);
      lp_value_destruct(&ub_lp);
      lp_value_destruct(&lb_lp);

#else
      x_value = expr::rational(iv.mid());
#endif
    }

    // Set the value
    simple_model[var] = x_value;
  }

  // Convert the model to Sally model
  d_last_model = get_model_from_simple_model(simple_model);
  TRACE("dreal::model") << *d_last_model << std::endl;

  // Check if the model
  return check_model();
}
  
expr::model::ref dreal_internal::get_model() {
  return d_last_model;
}

expr::model::ref dreal_internal::get_model_from_simple_model(const term_to_rational_map& simple_model) {

  // Empty model
  expr::model::ref m = new expr::model(d_tm, false);

  term_to_rational_map::const_iterator it = simple_model.begin();

  for(; it != simple_model.end(); ++it) {

    expr::term_ref x = it->first;
    expr::rational x_dreal_value = it->second;
    dreal_term x_dreal = to_dreal_term(x);
    expr::value x_value;

    expr::term_ref x_type = d_tm.type_of(x);
    expr::term_op x_type_op = d_tm.term_of(x_type).op();

    switch (x_type_op) {
    case expr::TYPE_BOOL:
      if (x_dreal_value == expr::rational(0, 1)) {
        x_value = expr::value(false);
      } else {
        x_value = expr::value(true);
      }
      break;
    case expr::TYPE_REAL:
      x_value = expr::value(x_dreal_value);
      break;
    case expr::TYPE_INTEGER:
      x_value = expr::value(x_dreal_value);
      break;
    default:
      throw exception("Dreal error (unexpected model value)");      
    }
    // Add the association
    m->set_variable_value(x, x_value);
  }
  
  return m;
}

void dreal_internal::push() {
  d_ctx->Push(1);
  if (d_ctx_bounded) {
    d_ctx_bounded->Push(1);
  }
  d_assertions_size.push_back(d_assertions.size());
}

void dreal_internal::pop() {
  d_ctx->Pop(1);
  if (d_ctx_bounded) {
    d_ctx_bounded->Pop(1);
  }
  size_t size = d_assertions_size.back();
  d_assertions_size.pop_back();
  while (d_assertions.size() > size) {
    d_assertions.pop_back();
    d_assertions_dreal.pop_back();
  }
  d_last_check_status = solver::result::UNKNOWN;
}

void dreal_internal::gc() {
  d_conversion_cache->gc();
}


void dreal_internal::add_variable(expr::term_ref var, smt::solver::variable_class f_class) {
  // Remember the variables
  d_variables.push_back(var);
  // Declare in dreal
  dreal_term dreal_var = to_dreal_term(var);
  d_ctx->DeclareVariable(dreal_var.variable(), true);
  if (d_ctx_bounded) {
    double bound = d_options.get_double("dreal-bound");
    dreal_term upper_bound(bound);
    dreal_term lower_bound(-bound);
    d_ctx_bounded->DeclareVariable(dreal_var.variable(), lower_bound.expression(), upper_bound.expression(), true);
  }
}

void dreal_internal::gc_collect(const expr::gc_relocator& gc_reloc) {
  gc_reloc.reloc(d_assertions);
  gc_reloc.reloc(d_variables);
}

void dreal_internal::dreal_to_smtlib2(std::ostream& out) {
  out << "(set-option :produce-models true)" << std::endl;
  out << "(set-logic QF_NRA)" << std::endl;
  out << "(set-info :smt-lib-version 2.0)" << std::endl;
  out << std::endl;

  for (size_t i = 0; i < d_variables.size(); ++ i) {
    expr::term_ref variable = d_variables[i];
    dreal_term dreal_var = to_dreal_term(variable);
    out << "(declare-fun " << dreal_var.to_string() << " () "
        << d_tm.type_of(variable) << ")" << std::endl;
  }

  out << std::endl;
  
  for (unsigned i=0, e=d_assertions_dreal.size(); i<e; ++i) {
    dreal_term t(d_assertions_dreal[i]);
    out << "(assert " << t.to_smtlib2() << ")" << std::endl;
  }
  
  out << "(check-sat)" << std::endl;
}
  
}
}

#endif
