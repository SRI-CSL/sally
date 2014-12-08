/*
 * model.cpp
 *
 *  Created on: Nov 28, 2014
 *      Author: dejan
 */

#include "expr/model.h"
#include "utils/exception.h"

#include <sstream>

namespace sal2 {
namespace expr {

model::model(expr::term_manager& tm)
: d_term_manager(tm)
{}

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

expr::term_ref model::get_value(expr::term_ref var) const {
  const_iterator find = d_variable_to_value_map.find(var);
  if (find == d_variable_to_value_map.end()) {
    std::stringstream ss;
    ss << set_tm(d_term_manager) << "Variable " << var << " is not part of the model.";
    throw exception(ss.str());
  }
  return find->second;
}

bool model::has_value(expr::term_ref var) const {
  return d_variable_to_value_map.find(var) != d_variable_to_value_map.end();
}

model::const_iterator model::values_begin() const {
  return d_variable_to_value_map.begin();
}

model::const_iterator model::values_end() const {
  return d_variable_to_value_map.end();
}
}
}
