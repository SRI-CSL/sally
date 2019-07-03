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

#include "smt/smt2_output_wrapper.h"
#include "utils/name_transformer.h"
#include "expr/gc_relocator.h"

namespace sally {
namespace smt {

smt2_output_wrapper::smt2_output_wrapper(expr::term_manager& tm, const options& opts, utils::statistics& stats, solver* solver, std::string filename)
: smt::solver("smt2_wrapper[" + filename + "]", tm, opts, stats)
, d_solver(solver)
, d_output(filename.c_str())
, d_total_assertions_count(0)
, d_vars_added(false)
{
  // Setup the stream
  output::set_output_language(d_output, output::MCMT);
  output::set_term_manager(d_output, &d_tm);
  output::set_use_lets(d_output, !opts.has_option("no-lets"));

  // Models by default
  d_output << "(set-option :produce-models true)" << std::endl;

  // Unsat cores if supported
  if (solver->supports(solver::UNSAT_CORE)) {
    d_output << "(set-option :produce-unsat-cores true)" << std::endl;
  }

  // Interpolation if supported
  if (solver->supports(solver::INTERPOLATION)) {
    d_output << "(set-option :produce-interpolants true)" << std::endl;
  }

  // If logic set, set it
  if (opts.has_option("solver-logic") > 0) {
    d_output << "(set-logic " << opts.get_string("solver-logic") << ")" << std::endl;
  }
}

smt2_output_wrapper::~smt2_output_wrapper() {
  delete d_solver;
}

bool smt2_output_wrapper::supports(feature f) const {
  return d_solver->supports(f);
}

void smt2_output_wrapper::add(expr::term_ref f, formula_class f_class) {
  assert(d_vars_added);

  assertion a(d_total_assertions_count ++, f, f_class);
  d_assertions.push_back(a);

  bool needs_annotation = d_solver->supports(solver::UNSAT_CORE) || d_solver->supports(solver::INTERPOLATION);

  d_output << "(assert ";
  if (needs_annotation) {
    d_output << "(! ";
  }
  d_output << f;
  if (d_solver->supports(solver::UNSAT_CORE)) {
    d_output << " :named a" << a.index;
  }
  if (d_solver->supports(solver::INTERPOLATION)) {
    if (a.f_class == CLASS_B) {
      d_output << " :interpolation-group B";
    } else {
      d_output << " :interpolation-group A";
    }
  }
  if (needs_annotation) {
    d_output << ")";
  }
  d_output << ")" << std::endl;

  d_solver->add(f, f_class);
}

solver::result smt2_output_wrapper::check() {
  d_output << "(check-sat)" << std::endl;
  return d_solver->check();
}

expr::model::ref smt2_output_wrapper::get_model() const {
  std::ofstream& out_nonconst = const_cast<smt2_output_wrapper*>(this)->d_output;
  out_nonconst << "(get-value (";
  std::set<expr::term_ref>::const_iterator it;
  bool space = false;
  for (it = d_A_variables.begin(); it != d_A_variables.end(); ++ it, space = true) {
    if (space) { out_nonconst << " "; }
    out_nonconst << *it << std::endl;
  }
  for (it = d_T_variables.begin(); it != d_T_variables.end(); ++ it, space = true) {
    if (space) { out_nonconst << " "; }
    out_nonconst << *it << std::endl;
  }
  for (it = d_B_variables.begin(); it != d_B_variables.end(); ++ it, space = true) {
    if (space) { out_nonconst << " "; }
    out_nonconst << *it << std::endl;
  }
  out_nonconst << "))" << std::endl;

  return d_solver->get_model();
}

void smt2_output_wrapper::push() {
  d_output << "(push 1)" << std::endl;
  d_solver->push();

  d_assertions_size.push_back(d_assertions.size());
}

void smt2_output_wrapper::pop() {
  d_output << "(pop 1)" << std::endl;
  d_solver->pop();

  size_t size = d_assertions_size.back();
  d_assertions_size.pop_back();
  while (d_assertions.size() > size) {
    d_assertions.pop_back();
  }
}

void smt2_output_wrapper::generalize(generalization_type type, std::vector<expr::term_ref>& projection_out) {
  d_solver->generalize(type, projection_out);
}

void smt2_output_wrapper::generalize(generalization_type type, expr::model::ref m, std::vector<expr::term_ref>& projection_out) {
  d_solver->generalize(type, m, projection_out);
}

void smt2_output_wrapper::interpolate(std::vector<expr::term_ref>& out) {
  d_output << "(get-interpolant (A))" << std::endl;
  d_solver->interpolate(out);
}

void smt2_output_wrapper::get_unsat_core(std::vector<expr::term_ref>& out) {
  d_output << "(get-unsat-core)" << std::endl;
  d_solver->get_unsat_core(out);
}

void smt2_output_wrapper::add_variable(expr::term_ref var, variable_class f_class) {
  d_output << "(declare-fun " << var << " () " << d_tm.type_of(var) << ")" << std::endl;
  solver::add_variable(var, f_class);
  d_solver->add_variable(var, f_class);
  d_vars_added = true;
}

void smt2_output_wrapper::gc_collect(const expr::gc_relocator& gc_reloc) {
  // Collect the solver
  solver::gc_collect(gc_reloc);
  // Collect the assertions
  for (size_t i = 0; i < d_assertions.size(); ++ i) {
    gc_reloc.reloc(d_assertions[i].f);
  }
}

}
}
