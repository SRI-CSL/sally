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

#include "smt/delayed_wrapper.h"

namespace sally {
namespace smt {

delayed_wrapper::delayed_wrapper(std::string name, expr::term_manager& tm, const options& opts, utils::statistics& stats, solver* s)
: solver(name, tm, opts, stats)
, d_solver(s)
, d_index(0)
, d_scope(0)
{
}

delayed_wrapper::~delayed_wrapper() {
  delete d_solver;
}

bool delayed_wrapper::supports(feature f) const {
  return d_solver->supports(f);
}

void delayed_wrapper::add(expr::term_ref f, formula_class f_class) {
  d_assertions.push_back(assertion(f, f_class));
}

void delayed_wrapper::flush() {
  for (; d_index < d_assertions.size(); ++ d_index) {
    if (d_scope < d_assertions_size.size() && d_index == d_assertions_size[d_scope]) {
      d_scope ++;
      d_solver->push();
    }
    d_solver->add(d_assertions[d_index].f, d_assertions[d_index].f_class);
  }
}

solver::result delayed_wrapper::check() {
  flush();
  return d_solver->check();
}

void delayed_wrapper::check_model() {
  d_solver->check_model();
}

expr::model::ref delayed_wrapper::get_model() const {
  return d_solver->get_model();
}

void delayed_wrapper::push() {
  d_assertions_size.push_back(d_assertions.size());
}

void delayed_wrapper::pop() {
  // Pop the assertions stack
  size_t size = d_assertions_size.back();
  d_assertions_size.pop_back();
  while (d_assertions.size() > size) {
    d_assertions.pop_back();
  }
  // If we went below next one to process, also update
  if (d_assertions.size() < d_index) {
    d_index = d_assertions.size();
  }
  // If scope went below currently processed, also update
  if (d_assertions_size.size() < d_scope) {
    d_scope = d_assertions_size.size();
    d_solver->pop();
  }
}

void delayed_wrapper::generalize(generalization_type type, std::vector<expr::term_ref>& out) {
  d_solver->generalize(type, out);
}

void delayed_wrapper::interpolate(std::vector<expr::term_ref>& out) {
  d_solver->interpolate(out);
}

void delayed_wrapper::get_unsat_core(std::vector<expr::term_ref>& out) {
  d_solver->get_unsat_core(out);
}

void delayed_wrapper::add_variable(expr::term_ref var, variable_class f_class) {
  d_solver->add_variable(var, f_class);
}

void delayed_wrapper::gc_collect(const expr::gc_relocator& gc_reloc) {
  solver::gc_collect(gc_reloc);
}

void delayed_wrapper::set_hint(expr::model::ref m) {
  flush();
  d_solver->set_hint(m);
}

}
}

