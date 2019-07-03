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
#ifdef WITH_DREAL

#include <iostream>

#include "d4y2.h"

#include "expr/term_manager.h"
#include "expr/rational.h"
#include "smt/yices2/yices2.h"
#include "smt/dreal/dreal.h"
#include "utils/trace.h"
#include "smt/delayed_wrapper.h"
#include "smt/factory.h"

namespace sally {
namespace smt {

size_t d4y2::s_instance = 0;

d4y2::d4y2(expr::term_manager& tm, const options& opts, utils::statistics& stats)
: solver("d4y2", tm, opts, stats)
, d_last_dreal4_result(UNKNOWN)
, d_last_yices2_result(UNKNOWN)
{
  d_dreal4 = factory::mk_solver("dreal", tm, opts, stats);
  d_yices2 = new delayed_wrapper("yices2_delayed", tm, opts, stats, factory::mk_solver("yices2", tm, opts, stats));
  s_instance ++;
}

d4y2::~d4y2() {
  delete d_dreal4;
  delete d_yices2;
  s_instance --;
}

void d4y2::add(expr::term_ref f, formula_class f_class) {
  TRACE("d4y2") << "d4y2[" << s_instance << "]: adding " << f << std::endl;
  d_dreal4->add(f, f_class);
  d_yices2->add(f, f_class);
  d_last_dreal4_result = UNKNOWN;
  d_last_yices2_result = UNKNOWN;
}

solver::result d4y2::check() {
  TRACE("d4y2") << "d4y2[" << s_instance << "]: check()" << std::endl;
  TRACE("d4y2") << "d4y2[" << s_instance << "]: running dreal" << std::endl;
  d_last_dreal4_result = d_dreal4->check();
  TRACE("d4y2") << "d4y2[" << s_instance << "]: dreal says " << d_last_dreal4_result << std::endl;
  if (d_last_dreal4_result != UNKNOWN) {
    d_last_yices2_result = UNKNOWN;
    return d_last_dreal4_result;
  } else {
    if (d_opts.get_bool("d4y2-model-as-hint")) {
      expr::model::ref dreal_model = d_dreal4->get_model();
      TRACE("d4y2::hint") << "d4y2[" << s_instance << "]: setting hint:" << *dreal_model << std::endl;
      if (dreal_model) {
        d_yices2->set_hint(dreal_model);
      }
    }
    TRACE("d4y2") << "d4y2[" << s_instance << "]: running yices" << std::endl;
    d_last_yices2_result = d_yices2->check();
    TRACE("d4y2") << "d4y2[" << s_instance << "]: yices says " << d_last_yices2_result << std::endl;
    return d_last_yices2_result;
  }
}

solver::result d4y2::check_relaxed() {
  TRACE("d4y2") << "d4y2[" << s_instance << "]: check_relaxed()" << std::endl;
  if (d_opts.get_bool("d4y2-relaxed-check")) {
    d_last_dreal4_result = d_dreal4->check();
    d_last_yices2_result = UNKNOWN;
    return d_last_dreal4_result;
  } else {
    return check();
  }
}

expr::model::ref d4y2::get_model() const {
  TRACE("d4y2") << "d4y2[" << s_instance << "]: get_model()" << std::endl;
  if (d_last_dreal4_result == SAT) {
    return d_dreal4->get_model();
  } else {
    assert(d_last_yices2_result == SAT);
    return d_yices2->get_model();
  }
}

void d4y2::push() {
  TRACE("d4y2") << "d4y2[" << s_instance << "]: push()" << std::endl;
  d_yices2->push();
  d_dreal4->push();
  d_last_dreal4_result = UNKNOWN;
  d_last_yices2_result = UNKNOWN;
}

void d4y2::pop() {
  TRACE("d4y2") << "d4y2[" << s_instance << "]: pop()" << std::endl;
  d_yices2->pop();
  d_dreal4->pop();
  d_last_dreal4_result = UNKNOWN;
  d_last_yices2_result = UNKNOWN;
}

void d4y2::add_variable(expr::term_ref var, variable_class f_class) {
  solver::add_variable(var, f_class);
  d_yices2->add_variable(var, f_class);
  d_dreal4->add_variable(var, f_class);
}

bool d4y2::supports(feature f) const {
  return false;
}

void d4y2::gc() {
  d_yices2->gc();
  d_dreal4->gc();
}

void d4y2::gc_collect(const expr::gc_relocator& gc_reloc) {
  solver::gc_collect(gc_reloc);
}

}
}

#endif
#endif
