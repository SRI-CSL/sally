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

#include "expr/model.h"
#include "expr/term_visitor.h"
#include "utils/exception.h"
#include "utils/trace.h"

#include <sstream>
#include <cassert>
#include <iostream>

namespace sally {
namespace expr {

model::model(expr::term_manager& tm, bool undef_to_default)
: d_tm(tm)
, d_undef_to_default(undef_to_default)
, d_true(true)
, d_false(false)
{
}

model::model(const model& other)
: d_tm(other.d_tm)
, d_undef_to_default(other.d_undef_to_default)
, d_variables(other.d_variables)
, d_variable_to_value_map(other.d_variable_to_value_map)
, d_true(true)
, d_false(false)
{
}

model& model::operator = (const model& other) {
  assert(&d_tm == &other.d_tm);
  if (this != &other) {
    d_undef_to_default = other.d_undef_to_default;
    d_variables = other.d_variables;
    d_variable_to_value_map = other.d_variable_to_value_map;
  }
  return *this;
}

void model::clear() {
  d_variable_to_value_map.clear();
  d_variables.clear();
}

void model::set_variable_value(expr::term_ref var, value v) {
  assert(d_tm.term_of(var).op() == expr::VARIABLE);
  iterator find = d_variable_to_value_map.find(var);
  if (find != d_variable_to_value_map.end()) {
    find->second = v;
  } else {
    d_variables.push_back(expr::term_ref_strong(d_tm, var));
    d_variable_to_value_map[var] = v;
  }
}

value model::get_variable_value(expr::term_ref var) const {
  expr::term_manager::substitution_map renaming;
  return get_variable_value(var, renaming);
}

value model::get_variable_value(expr::term_ref var, const expr::term_manager::substitution_map& var_renaming) const {
  assert(d_tm.term_of(var).op() == expr::VARIABLE);

  // Rename the variable if necessary
  expr::term_manager::substitution_map::const_iterator renaming_find = var_renaming.find(var);
  expr::term_ref var_to_evaluate;
  if (renaming_find == var_renaming.end()) {
    var_to_evaluate = var;
  } else {
    var_to_evaluate = renaming_find->second;
    TRACE("expr::model") << "get_variable_value(" << var << ") => evaluating " << var_to_evaluate << std::endl;
  }

  const_iterator find = d_variable_to_value_map.find(var_to_evaluate);
  if (find == d_variable_to_value_map.end()) {
    if (d_undef_to_default) {
      expr::term_ref type = d_tm.type_of(var_to_evaluate);
      value v;
      switch (d_tm.term_of(type).op()) {
      case TYPE_BOOL:
        v = value(false);
        break;
      case TYPE_INTEGER:
      case TYPE_REAL:
        v = value(rational());
        break;
      case TYPE_BITVECTOR:
        v = value(bitvector(d_tm.get_bitvector_size(type), 0));
        break;
      default:
        assert(false);
      }

      TRACE("expr::model") << "get_variable_value(" << var_to_evaluate << ") => [default] " << v << std::endl;
      return v;
    } else {
      std::stringstream ss;
      ss << set_tm(d_tm) << "Variable " << var_to_evaluate << " is not part of the model.";
      throw exception(ss.str());
    }
  } else {
    value v = find->second;
    TRACE("expr::model") << "get_variable_value(" << var_to_evaluate << ") => " << v << std::endl;
    return v;
  }
}

value model::get_term_value(expr::term_ref t) const {
  expr::term_manager::substitution_map renaming;
  return get_term_value(t, renaming);
}

value model::get_term_value(expr::term_ref t, const expr::term_manager::substitution_map& var_renaming) const {
  term_to_value_map cache;
  return get_term_value_internal(t, var_renaming, cache);
}

class evaluation_visitor {

  term_manager& d_tm;
  const expr::term_manager::substitution_map& d_var_renaming;
  model::term_to_value_map& d_cache;
  const model& d_model;

  value d_true;
  value d_false;

  std::vector<value> children_values;

public:

  evaluation_visitor(expr::term_manager& tm, const expr::term_manager::substitution_map& var_renaming, model::term_to_value_map& cache, const model& model)
  : d_tm(tm)
  , d_var_renaming(var_renaming)
  , d_cache(cache)
  , d_model(model)
  , d_true(true)
  , d_false(false)
  {}

  ~evaluation_visitor() {}

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

  // We visit only nodes that have not been evaluated yet, i.e. terms not in
  // the cache yet
  visitor_match_result match(term_ref t) {
    term_op op = d_tm.term_of(t).op();
    if (d_cache.find(t) == d_cache.end()) {
      // Visit children then this node
      if (op == VARIABLE) {
        // Don't go into the variable children (types)
        return VISIT_AND_BREAK;
      } else {
        return VISIT_AND_CONTINUE;
      }
    } else {
      // Don't visit children or this node
      return DONT_VISIT_AND_BREAK;
    }
  }

  void visit(term_ref t) {

    const term& t_term = d_tm.term_of(t);
    size_t t_size = t_term.size();
    term_op op = t_term.op();

    // Variables have children (type) but we don't want to evaluate them */
    if (op == VARIABLE) {
       d_cache[t] = d_model.get_variable_value(t, d_var_renaming);
       return;
    }

    // At this point, children have values, so we can evaluate
    // Not cached, evaluate children
    children_values.clear();

    for (size_t i = 0; i < t_size; ++ i) {
      expr::term_ref child = d_tm.term_of(t)[i];
      model::term_to_value_map::const_iterator find = d_cache.find(child);
      assert(find != d_cache.end());
      children_values.push_back(find->second);
    }

    // Now, compute the value
    value v;
    switch (op) {
    // ITE
    case TERM_ITE:
      if (children_values[0] == d_true) {
        v = children_values[1];
      } else {
        assert(children_values[0] == d_false);
        v = children_values[2];
      }
      break;
    // Equality
    case TERM_EQ:
      if (!children_values[0].is_null() && !children_values[1].is_null()) {
        v = value(children_values[0] == children_values[1]);
      }
      break;
    // Boolean terms
    case CONST_BOOL:
      v = d_tm.get_boolean_constant(t_term);
      break;
    case TERM_AND:
      v = d_true;
      for (size_t i = 0; i < t_size; ++ i) {
        if (children_values[i] == d_false) {
          v = d_false;
          break;
        }
      }
      break;
    case TERM_OR:
      v = d_false;
      for (size_t i = 0; i < t_size; ++ i) {
        if (children_values[i] == d_true) {
          v = d_true;
          break;
        }
      }
      break;
    case TERM_NOT:
      v = children_values[0] == d_true ? d_false : d_true;
      break;
    case TERM_IMPLIES:
      if (children_values[0] == d_true && children_values[1] == d_false) {
        v = d_false;
      } else {
        v = d_true;
      }
      break;
    case TERM_XOR: {
      size_t true_count = 0;
      for (size_t i = 0; i < t_size; ++ i) {
        if (children_values[i] == d_true) {
          true_count ++;
        }
      }
      if (true_count % 2) {
        v = d_true;
      } else {
        v = d_false;
      }
    }
    break;
    case CONST_RATIONAL:
      v = d_tm.get_rational_constant(d_tm.term_of(t));
      break;
    case TERM_ADD: {
      rational sum;
      for (size_t i = 0; i < t_size; ++ i) {
        sum += children_values[i].get_rational();
      }
      v = value(sum);
      break;
    }
    case TERM_SUB:
      if (t_size == 1) {
        v = value(-children_values[0].get_rational());
      } else {
        v = value(children_values[0].get_rational() - children_values[1].get_rational());
      }
      break;
    case TERM_MUL: {
      rational mul(1, 1);
      for (size_t i = 0; i < t_size; ++ i) {
        mul *= children_values[i].get_rational();
      }
      v = value(mul);
      break;
    }
    case TERM_DIV:
      v = value(children_values[0].get_rational() / children_values[1].get_rational());
      break;
    case TERM_LEQ:
      v = (children_values[0].get_rational() <= children_values[1].get_rational() ? d_true : d_false);
      break;
    case TERM_LT:
      v = (children_values[0].get_rational() < children_values[1].get_rational() ? d_true : d_false);
      break;
    case TERM_GEQ:
      v = (children_values[0].get_rational() >= children_values[1].get_rational() ? d_true : d_false);
      break;
    case TERM_GT:
      v = (children_values[0].get_rational() > children_values[1].get_rational() ? d_true : d_false);
      break;
    case TERM_TO_INT:
      v = value(children_values[0].get_rational().floor());
      break;
    case TERM_TO_REAL:
      v = children_values[0];
      break;
    case TERM_IS_INT:
      v = children_values[0].get_rational().is_integer() ? d_true : d_false;
      break;

    // Bit-vector terms
    case CONST_BITVECTOR:
      v = d_tm.get_bitvector_constant(t_term);
      assert(v.get_bitvector().size() == d_tm.get_bitvector_size(t));
      break;
    case TERM_BV_ADD: {
      bitvector bv = children_values[0].get_bitvector();
      for (size_t i = 1; i < children_values.size(); ++ i) {
        bv = bv.add(children_values[i].get_bitvector());
      }
      v = bv;
      assert(v.get_bitvector().size() == d_tm.get_bitvector_size(t));
      break;
    }
    case TERM_BV_SUB: {
      if (children_values.size() == 1) {
        v = children_values[0].get_bitvector().neg();
      } else if (children_values.size() == 2) {
        const bitvector& lhs = children_values[0].get_bitvector();
        const bitvector& rhs = children_values[1].get_bitvector();
        v = lhs.sub(rhs);
        assert(v.get_bitvector().size() == d_tm.get_bitvector_size(t));
      } else {
        assert(false);
      }
      break;
    }
    case TERM_BV_MUL: {
      bitvector bv = children_values[0].get_bitvector();
      for (size_t i = 1; i < children_values.size(); ++ i) {
        bv = bv.mul(children_values[i].get_bitvector());
      }
      v = bv;
      assert(v.get_bitvector().size() == d_tm.get_bitvector_size(t));
      break;
    }
    case TERM_BV_UDIV: { // NOTE: semantics of division is x/0 = 111...111
      const bitvector& lhs = children_values[0].get_bitvector();
      const bitvector& rhs = children_values[1].get_bitvector();
      v = lhs.udiv(rhs);
      assert(v.get_bitvector().size() == d_tm.get_bitvector_size(t));
      break;
    }
    case TERM_BV_SDIV: {
      const bitvector& lhs = children_values[0].get_bitvector();
      const bitvector& rhs = children_values[1].get_bitvector();
      v = lhs.sdiv(rhs);
      assert(v.get_bitvector().size() == d_tm.get_bitvector_size(t));
      break;
    }
    case TERM_BV_UREM: {
      const bitvector& lhs = children_values[0].get_bitvector();
      const bitvector& rhs = children_values[1].get_bitvector();
      v = lhs.urem(rhs);
      assert(v.get_bitvector().size() == d_tm.get_bitvector_size(t));
      break;
    }
    case TERM_BV_SREM: {
      const bitvector& lhs = children_values[0].get_bitvector();
      const bitvector& rhs = children_values[1].get_bitvector();
      v = lhs.srem(rhs);
      assert(v.get_bitvector().size() == d_tm.get_bitvector_size(t));
      break;
    }
    case TERM_BV_SMOD: {
      const bitvector& lhs = children_values[0].get_bitvector();
      const bitvector& rhs = children_values[1].get_bitvector();
      v = lhs.smod(rhs);
      assert(v.get_bitvector().size() == d_tm.get_bitvector_size(t));
      break;
    }
    case TERM_BV_XOR: {
      bitvector bv = children_values[0].get_bitvector();
      for (size_t i = 1; i < children_values.size(); ++ i) {
        bv = bv.bvxor(children_values[i].get_bitvector());
      }
      v = bv;
      assert(v.get_bitvector().size() == d_tm.get_bitvector_size(t));
      break;
    }
    case TERM_BV_SHL: {
      const bitvector& lhs = children_values[0].get_bitvector();
      const bitvector& rhs = children_values[1].get_bitvector();
      v = lhs.shl(rhs);
      assert(v.get_bitvector().size() == d_tm.get_bitvector_size(t));
      break;
    }
    case TERM_BV_LSHR: {
      const bitvector& lhs = children_values[0].get_bitvector();
      const bitvector& rhs = children_values[1].get_bitvector();
      v = lhs.lshr(rhs);
      assert(v.get_bitvector().size() == d_tm.get_bitvector_size(t));
      break;
    }
    case TERM_BV_ASHR: {
      const bitvector& lhs = children_values[0].get_bitvector();
      const bitvector& rhs = children_values[1].get_bitvector();
      v = lhs.ashr(rhs);
      assert(v.get_bitvector().size() == d_tm.get_bitvector_size(t));
      break;
    }
    case TERM_BV_NOT:
      v = children_values[0].get_bitvector().bvnot();
      assert(v.get_bitvector().size() == d_tm.get_bitvector_size(t));
      break;
    case TERM_BV_AND: {
      bitvector bv = children_values[0].get_bitvector();
      for (size_t i = 1; i < children_values.size(); ++ i) {
        bv = bv.bvand(children_values[i].get_bitvector());
      }
      v = bv;
      assert(v.get_bitvector().size() == d_tm.get_bitvector_size(t));
      break;
    }
    case TERM_BV_OR: {
      bitvector bv = children_values[0].get_bitvector();
      for (size_t i = 1; i < children_values.size(); ++ i) {
        bv = bv.bvor(children_values[i].get_bitvector());
      }
      v = bv;
      assert(v.get_bitvector().size() == d_tm.get_bitvector_size(t));
      break;
    }
    case TERM_BV_NAND:
      assert(false);
      break;
    case TERM_BV_NOR:
      assert(false);
      break;
    case TERM_BV_XNOR:
      assert(false);
      break;
    case TERM_BV_CONCAT: {
      bitvector bv = children_values[0].get_bitvector();
      for (size_t i = 1; i < children_values.size(); ++ i) {
        bv = bv.concat(children_values[i].get_bitvector());
      }
      v = bv;
      assert(v.get_bitvector().size() == d_tm.get_bitvector_size(t));
      break;
    }
    case TERM_BV_EXTRACT: {
      size_t low = d_tm.get_bitvector_extract(t_term).low;
      size_t high = d_tm.get_bitvector_extract(t_term).high;
      v = children_values[0].get_bitvector().extract(low, high);
      assert(v.get_bitvector().size() == d_tm.get_bitvector_size(t));
      break;
    }
    case TERM_BV_ULEQ: {
      const bitvector& lhs = children_values[0].get_bitvector();
      const bitvector& rhs = children_values[1].get_bitvector();
      v = lhs.uleq(rhs);
      break;
    }
    case TERM_BV_SLEQ: {
      const bitvector& lhs = children_values[0].get_bitvector();
      const bitvector& rhs = children_values[1].get_bitvector();
      v = lhs.sleq(rhs);
      break;
    }
    case TERM_BV_ULT: {
      const bitvector& lhs = children_values[0].get_bitvector();
      const bitvector& rhs = children_values[1].get_bitvector();
      v = lhs.ult(rhs);
      break;
    }
    case TERM_BV_SLT: {
      const bitvector& lhs = children_values[0].get_bitvector();
      const bitvector& rhs = children_values[1].get_bitvector();
      v = lhs.slt(rhs);
      break;
    }
    case TERM_BV_UGEQ: {
      const bitvector& lhs = children_values[0].get_bitvector();
      const bitvector& rhs = children_values[1].get_bitvector();
      v = lhs.ugeq(rhs);
      break;
    }
    case TERM_BV_SGEQ: {
      const bitvector& lhs = children_values[0].get_bitvector();
      const bitvector& rhs = children_values[1].get_bitvector();
      v = lhs.sgeq(rhs);
      break;
    }
    case TERM_BV_UGT: {
      const bitvector& lhs = children_values[0].get_bitvector();
      const bitvector& rhs = children_values[1].get_bitvector();
      v = lhs.ugt(rhs);
      break;
    }
    case TERM_BV_SGT: {
      const bitvector& lhs = children_values[0].get_bitvector();
      const bitvector& rhs = children_values[1].get_bitvector();
      v = lhs.sgt(rhs);
      break;
    }
    default:
      assert(false);
    }

    assert(!v.is_null());

    TRACE("expr::model") << "get_term_value_internal(" << t << ") => " << v << std::endl;

    // Remember the cache
    d_cache[t] = v;
  }
};


value model::get_term_value_internal(expr::term_ref t, const expr::term_manager::substitution_map& var_renaming, term_to_value_map& cache) const {
  evaluation_visitor visitor(d_tm, var_renaming, cache, *this);
  term_visit_topological<evaluation_visitor, term_ref, term_ref_hasher> visit_topological(visitor);
  visit_topological.run(t);
  return cache[t];
}

bool model::is_true(expr::term_ref f) const {
  expr::term_manager::substitution_map renaming;
  return is_true(f, renaming);
}

bool model::is_true(expr::term_ref f, const expr::term_manager::substitution_map& var_renaming) const {
  return get_term_value(f, var_renaming) == d_true;
}

bool model::is_false(expr::term_ref f) const {
  expr::term_manager::substitution_map renaming;
  return is_false(f, renaming);
}

bool model::is_false(expr::term_ref f, const expr::term_manager::substitution_map& var_renaming) const {
  return get_term_value(f, var_renaming) == d_false;
}

bool model::has_value(expr::term_ref var) const {
  assert(d_tm.term_of(var).op() == expr::VARIABLE);
  return d_variable_to_value_map.find(var) != d_variable_to_value_map.end();
}

model::const_iterator model::values_begin() const {
  return d_variable_to_value_map.begin();
}

model::const_iterator model::values_end() const {
  return d_variable_to_value_map.end();
}

void model::restrict_vars_to(const expr::term_manager::substitution_map& subst) {
  typedef expr::term_manager::substitution_map substitution_map;

  substitution_map::const_iterator it;

  // Rename the variables in the value map
  term_to_value_map variable_to_value_map_new;
  for (it = subst.begin(); it != subst.end(); ++ it) {
    term_ref x = it->first;
    term_ref x_new = it->second;
    assert(has_value(x));
    variable_to_value_map_new[x_new] = get_variable_value(x);
  }
  d_variable_to_value_map.swap(variable_to_value_map_new);

  // Rename the variables in the model
  std::vector<term_ref_strong> variables_new;
  for (size_t i = 0; i < d_variables.size(); ++ i) {
    term_ref x = d_variables[i];
    it = subst.find(x);
    if (it != subst.end()) {
      variables_new.push_back(term_ref_strong(d_tm, it->second));
    }
  }
}


void model::to_stream(std::ostream& out) const {
  for (const_iterator it = values_begin(); it != values_end(); ++ it) {
    out << "(" << it->first << " " << it->second << ")" << std::endl;
  }
}

std::ostream& operator << (std::ostream& out, const model& m) {
  m.to_stream(out);
  return out;
}

std::ostream& operator << (std::ostream& out, const model::ref& m_ref) {
  m_ref->to_stream(out);
  return out;
}

}
}
