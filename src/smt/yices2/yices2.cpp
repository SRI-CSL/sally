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

/*
 * BD: added this to work around issues with <stdint.h>. Without this,
 * the macro UINT32_MAX may not be defined in C++ even if you include
 * <stdint.h>.
 *
 * This should not be necessary for recent C++ compilers.
 */
#define __STDC_LIMIT_MACROS 1

#include <gmp.h>
#include <boost/unordered_map.hpp>

#include <iostream>
#include <fstream>
#include <iomanip>

#include "expr/term.h"
#include "expr/term_manager.h"
#include "expr/rational.h"
#include "smt/yices2/yices2.h"
#include "smt/yices2/yices2_internal.h"
#include "utils/trace.h"

#define unused_var(x) { (void) x; }

namespace sally {
namespace smt {

yices2::yices2(expr::term_manager& tm, const options& opts, utils::statistics& stats)
: solver("yices2", tm, opts, stats)
{
  d_internal = new yices2_internal(tm, opts);
}

yices2::~yices2() {
  delete d_internal;
}

void yices2::add(expr::term_ref f, formula_class f_class) {
  TRACE("yices2") << "yices2[" << d_internal->instance() << "]: adding " << f << std::endl;
  d_internal->add(f, f_class);
}

solver::result yices2::check() {
  TRACE("yices2") << "yices2[" << d_internal->instance() << "]: check()" << std::endl;
  return d_internal->check();
}

bool yices2::is_consistent() {
  TRACE("yices2") << "yices2[" << d_internal->instance() << "]: is_consistent()" << std::endl;
  return d_internal->is_consistent();
}

expr::model::ref yices2::get_model() const {
  TRACE("yices2") << "yices2[" << d_internal->instance() << "]: get_model()" << std::endl;
  return d_internal->get_model();
}

void yices2::push() {
  TRACE("yices2") << "yices2[" << d_internal->instance() << "]: push()" << std::endl;
  d_internal->push();
}

void yices2::pop() {
  TRACE("yices2") << "yices2[" << d_internal->instance() << "]: pop()" << std::endl;
  d_internal->pop();
}


void yices2::generalize(generalization_type type, std::vector<expr::term_ref>& projection_out) {
  TRACE("yices2") << "yices2[" << d_internal->instance() << "]: generalizing" << std::endl;
  assert(!d_B_variables.empty());
  d_internal->generalize(type, projection_out);
}

void yices2::generalize(generalization_type type, expr::model::ref m, std::vector<expr::term_ref>& projection_out) {
  TRACE("yices2") << "yices2[" << d_internal->instance() << "]: generalizing" << std::endl;
  assert(!d_B_variables.empty());
  d_internal->generalize(type, m, projection_out);
}

void yices2::add_variable(expr::term_ref var, variable_class f_class) {
  solver::add_variable(var, f_class);
  d_internal->add_variable(var, f_class);
}

void yices2::set_hint(expr::model::ref m) {
  d_internal->set_hint(m);
}


void yices2::gc() {
  d_internal->gc();
}

void yices2::gc_collect(const expr::gc_relocator& gc_reloc) {
  solver::gc_collect(gc_reloc);
  d_internal->gc_collect(gc_reloc);
}

}
}

#endif
