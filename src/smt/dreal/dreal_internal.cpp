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
#include "expr/term_visitor.h"
#include "utils/output.h"

#include <iostream>
#include <fstream>

using namespace dreal;

namespace sally {
namespace smt {

size_t dreal_internal::s_instances = 0;

dreal_internal::dreal_internal(expr::term_manager& tm, const options& opts)
  : d_tm(tm)
  , d_ctx(NULL)
  , d_conversion_cache(0)
  , d_last_check_status(solver::result::UNKNOWN)
  , d_config(NULL)
  , d_instance(s_instances)
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

  //default precision
  double prec = 0.001;
  if (opts.has_option("dreal-precision")) {
    prec = opts.get_double("dreal-precision");
    if (prec == 0.0) {
      // If no valid conversion could be performed, the function
      // returns zero (0.0).
      TRACE("dreal") << "dreal: it could not convert " << opts.get_string("dreal-precision")
		     << " to a double";
    } else {
      d_config->mutable_precision() = prec;
    }
  }

  if (opts.has_option("dreal-polytope")) {
    d_config->mutable_use_polytope() = true;
  }
  
  // The context
  d_ctx = new Context {*d_config};
  if (!d_ctx) {
    throw exception("Dreal error (context creation)");
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

public:

  to_dreal_visitor(expr::term_manager& tm, dreal_internal& dreal,
		   dreal_term_cache& cache)
  : d_tm(tm)
  , d_dreal(dreal)
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
  to_dreal_visitor visitor(d_tm, *this, *d_conversion_cache);
  expr::term_visit_topological<to_dreal_visitor, expr::term_ref, expr::term_ref_hasher>
    topological_visit(visitor);
  topological_visit.run(ref);
  dreal_term result = d_conversion_cache->get_term_cache(ref);
  assert(!result.is_null_term());
  return result;
}

void dreal_internal::add(expr::term_ref ref, solver::formula_class f_class) {
  // Remember the assertions
  expr::term_ref_strong ref_strong(d_tm, ref);
  d_assertions.push_back(ref_strong);
  d_assertion_classes.push_back(f_class);

  // Assert to dreal
  dreal_term dreal_t = to_dreal_term(ref);
  assert(dreal_t.is_formula());
  Formula f = dreal_t.formula();
  d_assertions_dreal.push_back(f);
  const Variables& vars = f.GetFreeVariables();
  for (Variables::const_iterator it = vars.begin(), et = vars.end(); it!=et; ++it) {
    const Variable& v = *it;
    d_ctx->DeclareVariable(v);
    d_assertion_vars.insert(v);
  }
  TRACE("dreal") << dreal_t.to_smtlib2() << std::endl;
  d_ctx->Assert(f);
  d_last_check_status = solver::UNKNOWN;
}

solver::result dreal_internal::check() {
  if (std::experimental::optional<Box> res = d_ctx->CheckSat()) {
    // If sat then dreal returns a mapping from a variable to an interval.
    // We return sat only if all intervals are singleton
    if (get_dreal_model(*res)) {
      d_last_check_status = solver::SAT;
    } else {
      d_last_check_status = solver::UNKNOWN;
    }
  } else {
    d_last_check_status = solver::UNSAT;    
  }

  return d_last_check_status;
}

bool dreal_internal::get_dreal_model(const Box& model) {
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

//  assert(!variables.empty());
  
  // See which variables we have to reason about
  d_last_model.clear();
  for (size_t i = 0; i < variables.size(); ++ i) {
    expr::term_ref var = variables[i];
    dreal_term dreal_var = to_dreal_term(var);
    assert(dreal_var.is_variable());
    
    const ibex::Interval& iv = model[dreal_var.variable()];
    if (iv.is_unbounded()) {
      goto NO_MODEL_FOUND;
    }

    double value;
    
    // if (iv.lb() != iv.ub()) {
    //   goto NO_MODEL_FOUND;
    // } else {
    //   value = iv.lb();
    // }
    
    double dist = (iv.lb() > iv.ub() ? iv.lb() - iv.ub(): iv.ub() - iv.lb());
    if (dist > d_ctx->config().precision()) {
      goto NO_MODEL_FOUND;
    } else {
      value = iv.mid();
    }
    d_last_model[var] = value;
  }
  return true;
  
  NO_MODEL_FOUND:
  std::cerr << "Warning: dreal produced a model but at least one variable was mapped "
	    << "to an interval that cannot be approximated to a single value with precision "
	    << d_ctx->config().precision() << "." << std::endl
	    << "delta-sat with delta =  " << d_ctx->config().precision() << std::endl
	    << model << std::endl;
  d_last_model.clear();  
  return false;
}
  
expr::model::ref dreal_internal::get_model() {
  assert(d_last_check_status == solver::SAT);
  assert(d_A_variables.size() > 0 || d_B_variables.size() > 0);
  assert(!d_last_model.empty());

  // Clear any data already there
  expr::model::ref m = new expr::model(d_tm, false);
  for(dreal_model_t::iterator it = d_last_model.begin(), et = d_last_model.end(); it!=et; ++it) {
    expr::term_ref var = it->first;
    double dreal_value = it->second;
    dreal_term dreal_var = to_dreal_term(var);
    expr::term_ref var_type = d_tm.type_of(var);
    expr::value var_value;
    switch (d_tm.term_of(var_type).op()) {
    case expr::TYPE_BOOL: {
      if (dreal_value == 0) {
	var_value = expr::value(0);
      } else if (dreal_value == 1) {
	var_value = expr::value(1);
      } else {
	// If a boolean variable is declared but not used in any
	// formula then dreal will produce a default value for it that
	// it might not be 0 or 1.
	assert(dreal_var.is_variable());
	if (d_assertion_vars.count(dreal_var.variable()) <= 0) {
	  // We use 0 as default value
	  var_value = expr::value(0);
	} else {
	  std::stringstream ss;
	  ss << "Dreal error (unexpected boolean value " << dreal_var << "="<< dreal_value
	     << " in the model)";
	  throw exception(ss.str());
	}
      }
    }
      break;
    case expr::TYPE_REAL: {
      // The real mpq_t value
      mpq_t value;
      mpq_init(value);
      mpq_set_d(value, dreal_value);
      expr::rational rational_value(value);
      var_value = expr::value(rational_value);
      // Clear the temps
      mpq_clear(value);
    }
      break;
    case expr::TYPE_INTEGER: {
      // The integer mpz_t value
      mpz_t value;
      mpz_init(value);
      mpz_set_d(value, dreal_value);
      expr::rational rational_value(value);
      var_value = expr::value(rational_value);
      // Clear the temps
      mpz_clear(value);
    }
      break;
    default:;;
      throw exception("Dreal error (unexpected model value)");      
    }
    // Add the association
    m->set_variable_value(var, var_value);
  }
  
  return m;
}

void dreal_internal::push() {
  d_ctx->Push(1);
  d_assertions_size.push_back(d_assertions.size());
}

void dreal_internal::pop() {
  d_ctx->Pop(1);
  size_t size = d_assertions_size.back();
  d_assertions_size.pop_back();
  while (d_assertions.size() > size) {
    d_assertions.pop_back();
    d_assertion_classes.pop_back();
    d_assertions_dreal.pop_back();
  }
  d_last_check_status = solver::result::UNKNOWN;
}

void dreal_internal::gc() {
  d_conversion_cache->gc();
}


void dreal_internal::add_variable(expr::term_ref var, smt::solver::variable_class f_class) {
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

  // Convert to dreal early
  to_dreal_term(var);

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

void dreal_internal::gc_collect(const expr::gc_relocator& gc_reloc) {
  gc_reloc.reloc(d_assertions);
  gc_reloc.reloc(d_A_variables);
  gc_reloc.reloc(d_B_variables);
  gc_reloc.reloc(d_T_variables);
}

void dreal_internal::dreal_to_smtlib2(std::ostream& out) {
  out << "(set-option :produce-models true)" << std::endl;
  out << "(set-logic QF_NRA)" << std::endl;
  out << "(set-info :smt-lib-version 2.0)" << std::endl;
  out << std::endl;

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
  
  for (size_t i = 0; i < variables.size(); ++ i) {
    expr::term_ref variable = variables[i];
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
