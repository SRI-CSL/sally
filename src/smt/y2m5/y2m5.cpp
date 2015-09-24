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
#ifdef WITH_MATHSAT5

#include <iostream>

#include "expr/term.h"
#include "expr/term_manager.h"
#include "expr/rational.h"
#include "smt/y2m5/y2m5.h"
#include "smt/yices2/yices2.h"
#include "smt/mathsat5/mathsat5.h"
#include "utils/trace.h"
#include "smt/incremental_wrapper.h"
#include "smt/delayed_wrapper.h"
#include "smt/factory.h"

namespace sally {
namespace smt {

size_t y2m5::s_instance = 0;

class mathsat_constructor : public solver_constructor {
  expr::term_manager& d_tm;
  const options& d_opts;
  utils::statistics& d_stats;
public:
  mathsat_constructor(expr::term_manager& tm, const options& opts, utils::statistics& stats)
  : d_tm(tm), d_opts(opts), d_stats(stats) {}
  ~mathsat_constructor() {};
  solver* mk_solver() { return factory::mk_solver("mathsat5", d_tm, d_opts, d_stats); }
};

y2m5::y2m5(expr::term_manager& tm, const options& opts, utils::statistics& stats)
: solver("y2m5", tm, opts, stats)
, d_last_mathsat5_result(UNKNOWN)
, d_last_yices2_result(UNKNOWN)
{
  d_yices2 = factory::mk_solver("yices2", tm, opts, stats);
  if (opts.get_bool("y2m5-mathsat5-flatten")) {
    solver_constructor* constructor = new mathsat_constructor(tm, opts, stats);
    d_mathsat5 = new incremental_wrapper("mathsat5_nonincremental", tm, opts, stats, constructor);
  } else {
    d_mathsat5 = new delayed_wrapper("mathsat5_incremental", tm, opts, stats, factory::mk_solver("mathsat5", tm, opts, stats));
  }
  s_instance ++;
}

y2m5::~y2m5() {
  delete d_mathsat5;
  delete d_yices2;
  s_instance --;
}

void y2m5::add(expr::term_ref f, formula_class f_class) {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: adding " << f << std::endl;
  d_yices2->add(f, f_class);
  d_mathsat5->add(f, f_class);
  d_last_mathsat5_result = UNKNOWN;
  d_last_yices2_result = UNKNOWN;
}

solver::result y2m5::check() {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: check()" << std::endl;
  d_last_yices2_result = d_yices2->check();
  d_last_mathsat5_result = UNKNOWN;
  return d_last_yices2_result;
}

expr::model::ref y2m5::get_model() const {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: get_model()" << std::endl;
  assert(d_last_yices2_result == SAT);
  return d_yices2->get_model();
}

void y2m5::push() {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: push()" << std::endl;
  d_yices2->push();
  d_mathsat5->push();
  d_last_mathsat5_result = UNKNOWN;
  d_last_yices2_result = UNKNOWN;
}

void y2m5::pop() {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: pop()" << std::endl;
  d_yices2->pop();
  d_mathsat5->pop();
  d_last_mathsat5_result = UNKNOWN;
  d_last_yices2_result = UNKNOWN;
}


void y2m5::generalize(generalization_type type, std::vector<expr::term_ref>& out) {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: generalizing" << std::endl;
  assert(d_last_yices2_result == SAT);
  d_yices2->generalize(type, out);
}

void y2m5::interpolate(std::vector<expr::term_ref>& out) {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: interpolating" << std::endl;
  if (d_last_mathsat5_result == UNKNOWN) {
    d_last_mathsat5_result = d_mathsat5->check();
  }
  if (d_last_mathsat5_result != UNSAT) {
    // Check the model for correctness
    d_mathsat5->check_model();
  }
  assert(d_last_mathsat5_result == UNSAT);
  d_mathsat5->interpolate(out);
}

void y2m5::get_unsat_core(std::vector<expr::term_ref>& out) {
  TRACE("y2m5") << "y2m5[" << s_instance << "]: unsat core" << std::endl;
  if (d_last_mathsat5_result == UNKNOWN) {
    d_last_mathsat5_result = d_mathsat5->check();
  }
  assert(d_last_mathsat5_result == UNSAT);
  d_mathsat5->get_unsat_core(out);
}

void y2m5::add_variable(expr::term_ref var, variable_class f_class) {
  solver::add_variable(var, f_class);
  d_yices2->add_variable(var, f_class);
  d_mathsat5->add_variable(var, f_class);
}

bool y2m5::supports(feature f) const {
  switch (f) {
  case GENERALIZATION:
    return d_yices2->supports(f);
  case INTERPOLATION:
    return d_mathsat5->supports(f);
  case UNSAT_CORE:
    return d_mathsat5->supports(f);
  default:
    return false;
  }
}

void y2m5::gc() {
  d_yices2->gc();
  d_mathsat5->gc();
}

void y2m5::gc_collect(const expr::gc_relocator& gc_reloc) {
  solver::gc_collect(gc_reloc);
}

}
}

#endif
#endif
