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

#include "smt/incremental_wrapper.h"
#include "expr/gc_relocator.h"


namespace sally {
namespace smt {

incremental_wrapper::incremental_wrapper(std::string name, expr::term_manager& tm, const options& opts, utils::statistics& stats, solver_constructor* constructor)
: solver(name, tm, opts, stats)
, d_constructor(constructor)
{
  d_solver = d_constructor->mk_solver();
}

incremental_wrapper::~incremental_wrapper() {
  delete d_solver;
  delete d_constructor;
}

bool incremental_wrapper::supports(feature f) const {
  return d_solver->supports(f);
}

void incremental_wrapper::add(expr::term_ref f, formula_class f_class) {
  d_assertions.push_back(assertion(f, f_class));
}

solver::result incremental_wrapper::check() {

  delete d_solver;
  d_solver = d_constructor->mk_solver();

  // Initialize solver
  d_solver->add_variables(d_A_variables.begin(), d_A_variables.end(), CLASS_A);
  d_solver->add_variables(d_B_variables.begin(), d_B_variables.end(), CLASS_B);
  d_solver->add_variables(d_T_variables.begin(), d_T_variables.end(), CLASS_T);

  // Assert the formulas
  for (size_t i = 0; i < d_assertions.size(); ++ i) {
    d_solver->add(d_assertions[i].f, d_assertions[i].f_class);
  }

  // Check and interpolate
  return d_solver->check();
}

expr::model::ref incremental_wrapper::get_model() const {
  return d_solver->get_model();
}

void incremental_wrapper::push() {
  d_assertions_size.push_back(d_assertions.size());
}

void incremental_wrapper::pop() {
  size_t size = d_assertions_size.back();
  d_assertions_size.pop_back();
  while (d_assertions.size() > size) {
    d_assertions.pop_back();
  }
}

void incremental_wrapper::generalize(generalization_type type, std::vector<expr::term_ref>& out) {
  d_solver->generalize(type, out);
}

void incremental_wrapper::interpolate(std::vector<expr::term_ref>& out) {
  d_solver->interpolate(out);
}

void incremental_wrapper::get_unsat_core(std::vector<expr::term_ref>& out) {
  d_solver->get_unsat_core(out);
}

void incremental_wrapper::gc_collect(const expr::gc_relocator& gc_reloc) {
  solver::gc_collect(gc_reloc);
  for (size_t i = 0; i < d_assertions.size(); ++ i) {
    gc_reloc.reloc(d_assertions[i].f);
  }
}

}
}

