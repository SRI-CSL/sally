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

#include "smt/solver.h"
#include "expr/gc_relocator.h"

#include <cassert>
#include <iostream>

namespace sally {
namespace smt {

std::ostream& operator << (std::ostream& out, solver::result result) {
  switch (result) {
  case solver::SAT:
    out << "sat";
    break;
  case solver::UNSAT:
    out << "unsat";
    break;
  case solver::UNKNOWN:
    out << "unknown";
    break;
  }
  return out;
}

expr::term_ref solver::generalize(generalization_type type) {
  std::vector<expr::term_ref> projection_out;
  generalize(type, projection_out);
  return d_tm.mk_and(projection_out);
}

expr::term_ref solver::generalize(generalization_type type, expr::model::ref m) {
  std::vector<expr::term_ref> projection_out;
  generalize(type, m, projection_out);
  return d_tm.mk_and(projection_out);
}

expr::term_ref solver::interpolate() {
  std::vector<expr::term_ref> interpolation_out;
  interpolate(interpolation_out);
  return d_tm.mk_and(interpolation_out);
}

void solver::add_variable(expr::term_ref var, variable_class f_class) {

  assert(d_A_variables.find(var) == d_A_variables.end());
  assert(d_B_variables.find(var) == d_B_variables.end());
  assert(d_T_variables.find(var) == d_T_variables.end());

  switch (f_class) {
  case CLASS_A:
    d_A_variables.insert(var);
    break;
  case CLASS_B:
    d_B_variables.insert(var);
    break;
  case CLASS_T:
    d_T_variables.insert(var);
    break;
  default:
    assert(false);
  }
}

void solver::gc_collect(const expr::gc_relocator& gc_reloc) {
  gc_reloc.reloc(d_A_variables);
  gc_reloc.reloc(d_B_variables);
  gc_reloc.reloc(d_T_variables);
}

std::ostream& operator << (std::ostream& out, solver::formula_class fc) {
  switch(fc) {
  case solver::CLASS_A: out << "CLASS A"; break;
  case solver::CLASS_T: out << "CLASS_T"; break;
  case solver::CLASS_B: out << "CLASS B"; break;
  default:
    assert(false);
  }
  return out;
}

}
}
