/*
 * model.cpp
 *
 *  Created on: Nov 28, 2014
 *      Author: dejan
 */

#include "expr/model.h"
#include "utils/exception.h"

#include <sstream>
#include <cassert>
#include <iostream>

namespace sally {
namespace expr {

model::model(expr::term_manager& tm)
: d_term_manager(tm)
{
  d_true = tm.mk_boolean_constant(true);
  d_false = tm.mk_boolean_constant(false);
}

void model::clear() {
  d_variable_to_value_map.clear();
  d_variables.clear();
}

void model::set_value(expr::term_ref var, expr::term_ref value) {
  assert(d_term_manager.term_of(var).op() == expr::VARIABLE);
  iterator find = d_variable_to_value_map.find(var);
  if (find != d_variable_to_value_map.end()) {
    find->second = value;
  } else {
    d_variables.push_back(expr::term_ref_strong(d_term_manager, var));
    d_variable_to_value_map[var] = value;
  }
}

expr::term_ref model::get_variable_value(expr::term_ref t) const {
  assert(d_term_manager.term_of(t).op() == expr::VARIABLE);
  const_iterator find = d_variable_to_value_map.find(t);
  if (find == d_variable_to_value_map.end()) {
      std::stringstream ss;
      ss << set_tm(d_term_manager) << "Variable " << t << " is not part of the model.";
      throw exception(ss.str());
  } else {
    return find->second;
  }
}

expr::term_ref model::get_term_value(expr::term_ref t) {

  // If a variable and not in the model, we don't know how to evaluate
  if (d_term_manager.term_of(t).op() == expr::VARIABLE) {
    const_iterator find = d_variable_to_value_map.find(t);
    if (find == d_variable_to_value_map.end()) {
      std::stringstream ss;
      ss << set_tm(d_term_manager) << "Variable " << t << " is not part of the model.";
      throw exception(ss.str());
    }
    return find->second;
  } else {
    // Proper term, we have to evaluate, if not in the cache already
    const_iterator find = d_term_to_value_map.find(t);
    if (find != d_term_to_value_map.end()) {
      return find->second;
    }

    // Not cached, evaluate children
    size_t t_size = d_term_manager.term_of(t).size();
    std::vector<expr::term_ref> children_values;
    for (size_t i = 0; i < t_size; ++ i) {
      expr::term_ref child = d_term_manager.term_of(t)[i];
      expr::term_ref value = get_term_value(child);
      children_values.push_back(value);
    }

    // Arith value
    bool has_arith_value = false;
    expr::rational arith_value;

    // Now, compute the value
    expr::term_op op = d_term_manager.term_of(t).op();
    expr::term_ref value;
    switch (op) {
    // ITE
    case TERM_ITE:
      if (children_values[0] == d_true) {
        value = children_values[1];
      } else {
        assert(children_values[0] == d_false);
        value = children_values[2];
      }
      break;
      // Equality
    case TERM_EQ: {
      if (d_term_manager.equal_constants(children_values[0], children_values[1])) {
        value = d_true;
      } else {
        value = d_false;
      }
      break;
    }
    // Boolean terms
    case CONST_BOOL:
      value = t;
      break;
    case TERM_AND:
      value = d_true;
      for (size_t i = 0; i < t_size; ++ i) {
        if (children_values[i] == d_false) {
          value = d_false;
          break;
        }
      }
      break;
    case TERM_OR:
      value = d_false;
      for (size_t i = 0; i < t_size; ++ i) {
        if (children_values[i] == d_true) {
          value = d_true;
          break;
        }
      }
      break;
    case TERM_NOT:
      value = children_values[0] == d_true ? d_false : d_true;
      break;
    case TERM_IMPLIES:
      if (children_values[0] == d_true && children_values[1] == d_false) {
        value = d_false;
      } else {
        value = d_true;
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
        value = d_true;
      } else {
        value = d_false;
      }
    }
    break;
    // Arithmetic terms
    case CONST_INTEGER:
      value = t;
      break;
    case CONST_RATIONAL:
      value = t;
      break;
    case TERM_ADD:
      for (size_t i = 0; i < t_size; ++ i) {
        arith_value += expr::rational(d_term_manager, children_values[i]);
      }
      has_arith_value = true;
      break;
    break;
    case TERM_SUB:
      if (t_size == 1) {
        arith_value = -expr::rational(d_term_manager, children_values[0]);
      } else {
        arith_value = expr::rational(d_term_manager, children_values[0]) - expr::rational(d_term_manager, children_values[1]);
      }
      has_arith_value = true;
      break;
    case TERM_MUL:
      arith_value = expr::rational(d_term_manager, children_values[0]);
      for (size_t i = 1; i < t_size; ++ i) {
        arith_value *= expr::rational(d_term_manager, children_values[i]);
      }
      has_arith_value = true;
      break;
    case TERM_DIV:
      arith_value = expr::rational(d_term_manager, children_values[0]) / expr::rational(d_term_manager, children_values[1]);
      has_arith_value = true;
      break;
    case TERM_LEQ: {
      rational a(d_term_manager, children_values[0]);
      rational b(d_term_manager, children_values[1]);
      value = (a <= b ? d_true : d_false);
      break;
    }
    case TERM_LT: {
      rational a(d_term_manager, children_values[0]);
      rational b(d_term_manager, children_values[1]);
      value = (a < b ? d_true : d_false);
      break;
    }
    case TERM_GEQ: {
      rational a(d_term_manager, children_values[0]);
      rational b(d_term_manager, children_values[1]);
      value = (a >= b ? d_true : d_false);
      break;
    }
    case TERM_GT: {
      rational a(d_term_manager, children_values[0]);
      rational b(d_term_manager, children_values[1]);
      value = (a > b ? d_true : d_false);
      break;
    }

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

    if (has_arith_value) {
      if (d_term_manager.type_of(t) == d_term_manager.real_type()) {
        value = d_term_manager.mk_rational_constant(arith_value);
      } else {
        assert(arith_value.is_integer());
        value = d_term_manager.mk_integer_constant(arith_value.get_numerator());
      }
    }

    assert(!value.is_null());

    // Remember the cache
    d_term_to_value_map[t] = value;

    return value;
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
  assert(d_term_manager.term_of(var).op() == expr::VARIABLE);
  return d_variable_to_value_map.find(var) != d_variable_to_value_map.end();
}

model::const_iterator model::values_begin() const {
  return d_variable_to_value_map.begin();
}

model::const_iterator model::values_end() const {
  return d_variable_to_value_map.end();
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

}
}
