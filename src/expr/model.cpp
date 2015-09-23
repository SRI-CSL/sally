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
, d_term_to_value_map(other.d_term_to_value_map)
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
    d_term_to_value_map = other.d_term_to_value_map;
  }
  return *this;
}

model::model_refcounted::model_refcounted(model* model)
: d_model(model)
, d_refcount(0)
{
  attach();
}

model::model_refcounted::~model_refcounted() {
  assert(d_refcount == 0);
}

model* model::model_refcounted::get_model() {
  return d_model;
}

const model* model::model_refcounted::get_model() const {
  return d_model;
}

void model::model_refcounted::attach() {
  d_refcount ++;
}

void model::model_refcounted::detach() {
  assert(d_refcount > 0);
  d_refcount --;
  if (d_refcount == 0) {
    delete d_model;
    delete this;
  }
}

void model::clear() {
  d_variable_to_value_map.clear();
  d_term_to_value_map.clear();
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
  assert(d_tm.term_of(var).op() == expr::VARIABLE);
  const_iterator find = d_variable_to_value_map.find(var);
  if (find == d_variable_to_value_map.end()) {
    if (d_undef_to_default) {
      expr::term_ref type = d_tm.type_of(var);
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

      TRACE("expr::model") << "get_term_value(" << var << ") => [default] " << v << std::endl;
      return v;
    } else {
      std::stringstream ss;
      ss << set_tm(d_tm) << "Variable " << var << " is not part of the model.";
      throw exception(ss.str());
    }
  } else {
    return find->second;
  }
}

value model::get_term_value(expr::term_ref t) {

  TRACE("expr::model") << "get_term_value(" << t << ")" << std::endl;

  // If a variable and not in the model, we don't know how to evaluate
  if (d_tm.term_of(t).op() == expr::VARIABLE) {
    return get_variable_value(t);
  } else {
    // Proper term, we have to evaluate, if not in the cache already
    const_iterator find = d_term_to_value_map.find(t);
    if (find != d_term_to_value_map.end()) {
      TRACE("expr::model") << "get_term_value(" << t << ") => " << find->second << std::endl;
      return find->second;
    }

    // Not cached, evaluate children
    size_t t_size = d_tm.term_of(t).size();
    std::vector<value> children_values;
    for (size_t i = 0; i < t_size; ++ i) {
      expr::term_ref child = d_tm.term_of(t)[i];
      children_values.push_back(get_term_value(child));
    }

    // Now, compute the value
    expr::term_op op = d_tm.term_of(t).op();
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
      v = children_values[0] == children_values[1];
      break;
    // Boolean terms
    case CONST_BOOL:
      v = d_tm.get_boolean_constant(d_tm.term_of(t));
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
        v = value(children_values[0].get_rational() -children_values[1].get_rational());
      }
      break;
    case TERM_MUL: {
      rational mul(1, 0);
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

    // Bit-vector terms
    case CONST_BITVECTOR:
    case TERM_BV_ADD:
    case TERM_BV_SUB:
    case TERM_BV_MUL:
    case TERM_BV_UDIV: // NOTE: semantics of division is x/0 = 111...111
    case TERM_BV_SDIV:
    case TERM_BV_UREM:
    case TERM_BV_SREM:
    case TERM_BV_SMOD:
    case TERM_BV_XOR:
    case TERM_BV_SHL:
    case TERM_BV_LSHR:
    case TERM_BV_ASHR:
    case TERM_BV_NOT:
    case TERM_BV_AND:
    case TERM_BV_OR:
    case TERM_BV_NAND:
    case TERM_BV_NOR:
    case TERM_BV_XNOR:
    case TERM_BV_CONCAT:
    case TERM_BV_EXTRACT:
    case TERM_BV_ULEQ:
    case TERM_BV_SLEQ:
    case TERM_BV_ULT:
    case TERM_BV_SLT:
    case TERM_BV_UGEQ:
    case TERM_BV_SGEQ:
    case TERM_BV_UGT:
    case TERM_BV_SGT:
    default:
      assert(false);
    }

    assert(!v.is_null());

    TRACE("expr::model") << "get_term_value(" << t << ") => " << v << std::endl;

    // Remember the cache
    d_term_to_value_map[t] = v;

    return v;
  }
}

bool model::is_true(expr::term_ref f) {
  return get_term_value(f) == d_true;
}

/** Is the formula false in the model */
bool model::is_false(expr::term_ref f) {
  return get_term_value(f) == d_false;
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

void model::clear_cache() {
  d_term_to_value_map.clear();
}

void model::restrict_vars_to(const expr::term_manager::substitution_map& subst) {
  typedef expr::term_manager::substitution_map substitution_map;

  substitution_map::const_iterator it;

  // Clear the cache
  clear_cache();

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

model::ref::ref(model* model)
: d_model(0)
{
  if (model) {
    d_model = new model_refcounted(model);
  }
}

model::ref::ref(const ref& r)
: d_model(r.d_model)
{
  if (d_model) {
    d_model->attach();
  }
}

model::ref::~ref() {
  if (d_model) {
    d_model->detach();
  }
}

model::ref& model::ref::operator = (const ref& other)
{
  if (this != &other) {
    if (d_model) {
      d_model->detach();
    }
    d_model = other.d_model;
    if (d_model) {
      d_model->attach();
    }
  }
  return *this;
}

model::ref& model::ref::operator = (model* m)
{
  if (d_model) {
    d_model->detach();
    d_model = 0;
  }
  if (m) {
    d_model = new model_refcounted(m);
  }
  return *this;
}

model& model::ref::operator * () {
  assert(d_model);
  return *d_model->get_model();
}

const model& model::ref::operator * () const {
  assert(d_model);
  return *d_model->get_model();
}

model* model::ref::operator -> () {
  assert(d_model);
  return d_model->get_model();
}

const model* model::ref::operator -> () const {
  return d_model->get_model();
}

}
}
