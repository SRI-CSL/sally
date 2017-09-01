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

#ifdef WITH_YICES2
#ifdef WITH_Z3

#include <iostream>

#include "expr/term.h"
#include "expr/term_manager.h"
#include "expr/rational.h"
#include "smt/y2z3/y2z3.h"
#include "smt/yices2/yices2.h"
#include "smt/z3/z3.h"
#include "utils/trace.h"
#include "smt/incremental_wrapper.h"
#include "smt/delayed_wrapper.h"
#include "smt/factory.h"

namespace sally {
namespace smt {

size_t y2z3::s_instance = 0;

class mathsat_constructor : public solver_constructor {
  expr::term_manager& d_tm;
  const options& d_opts;
  utils::statistics& d_stats;
public:
  mathsat_constructor(expr::term_manager& tm, const options& opts, utils::statistics& stats)
  : d_tm(tm), d_opts(opts), d_stats(stats) {}
  ~mathsat_constructor() {};
  solver* mk_solver() { return factory::mk_solver("z3", d_tm, d_opts, d_stats); }
};

y2z3::y2z3(expr::term_manager& tm, const options& opts, utils::statistics& stats)
: solver("y2z3", tm, opts, stats)
, d_last_z3_result(UNKNOWN)
, d_last_yices2_result(UNKNOWN)
{
  d_yices2 = factory::mk_solver("yices2", tm, opts, stats);
  if (opts.get_bool("y2z3-z3-flatten")) {
    solver_constructor* constructor = new mathsat_constructor(tm, opts, stats);
    d_z3 = new incremental_wrapper("z3_nonincremental", tm, opts, stats, constructor);
  } else {
    d_z3 = new delayed_wrapper("z3_incremental", tm, opts, stats, factory::mk_solver("z3", tm, opts, stats));
  }
  s_instance ++;
}

y2z3::~y2z3() {
  delete d_z3;
  delete d_yices2;
  s_instance --;
}

void y2z3::add(expr::term_ref f, formula_class f_class) {
  TRACE("y2z3") << "y2z3[" << s_instance << "]: adding " << f << std::endl;
  d_yices2->add(f, f_class);
  d_z3->add(f, f_class);
  d_last_z3_result = UNKNOWN;
  d_last_yices2_result = UNKNOWN;
}

solver::result y2z3::check() {
  TRACE("y2z3") << "y2z3[" << s_instance << "]: check()" << std::endl;
  d_last_yices2_result = d_yices2->check();
  d_last_z3_result = UNKNOWN;
  return d_last_yices2_result;
}

expr::model::ref y2z3::get_model() const {
  TRACE("y2z3") << "y2z3[" << s_instance << "]: get_model()" << std::endl;
  assert(d_last_yices2_result == SAT);
  return d_yices2->get_model();
}

void y2z3::push() {
  TRACE("y2z3") << "y2z3[" << s_instance << "]: push()" << std::endl;
  d_yices2->push();
  d_z3->push();
  d_last_z3_result = UNKNOWN;
  d_last_yices2_result = UNKNOWN;
}

void y2z3::pop() {
  TRACE("y2z3") << "y2z3[" << s_instance << "]: pop()" << std::endl;
  d_yices2->pop();
  d_z3->pop();
  d_last_z3_result = UNKNOWN;
  d_last_yices2_result = UNKNOWN;
}

int y2z3::get_scope() const {
  return d_yices2->get_scope();
}

void y2z3::generalize(generalization_type type, std::vector<expr::term_ref>& out) {
  TRACE("y2z3") << "y2z3[" << s_instance << "]: generalizing" << std::endl;
  assert(d_last_yices2_result == SAT);
  d_yices2->generalize(type, out);
}

void y2z3::generalize(generalization_type type, expr::model::ref m, std::vector<expr::term_ref>& out) {
  TRACE("y2z3") << "y2z3[" << s_instance << "]: generalizing" << std::endl;
  d_yices2->generalize(type, m, out);
}

void y2z3::interpolate(std::vector<expr::term_ref>& out) {
  TRACE("y2z3") << "y2z3[" << s_instance << "]: interpolating" << std::endl;
  if (d_last_z3_result == UNKNOWN) {
    d_last_z3_result = d_z3->check();
  }
  d_z3->interpolate(out);
}

void y2z3::get_unsat_core(std::vector<expr::term_ref>& out) {
  TRACE("y2z3") << "y2z3[" << s_instance << "]: unsat core" << std::endl;
  if (d_last_z3_result == UNKNOWN) {
    d_last_z3_result = d_z3->check();
  }
  assert(d_last_z3_result == UNSAT);
  d_z3->get_unsat_core(out);
}

void y2z3::add_variable(expr::term_ref var, variable_class f_class) {
  solver::add_variable(var, f_class);
  d_yices2->add_variable(var, f_class);
  d_z3->add_variable(var, f_class);
}

bool y2z3::supports(feature f) const {
  switch (f) {
  case GENERALIZATION:
    return d_yices2->supports(f);
  case INTERPOLATION:
    return d_z3->supports(f);
  case UNSAT_CORE:
    return d_z3->supports(f);
  default:
    return false;
  }
}

void y2z3::gc() {
  d_yices2->gc();
  d_z3->gc();
}

void y2z3::gc_collect(const expr::gc_relocator& gc_reloc) {
  solver::gc_collect(gc_reloc);
}

void y2z3::get_assertions(std::vector<expr::term_ref>& out) const {
  d_yices2->get_assertions(out);
}

}
}

#endif
#endif
