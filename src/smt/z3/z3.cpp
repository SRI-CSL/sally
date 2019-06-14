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

#ifdef WITH_Z3

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
#include "smt/z3/z3.h"
#include "smt/z3/z3_internal.h"
#include "utils/trace.h"

#define unused_var(x) { (void) x; }

namespace sally {
namespace smt {

z3::z3(expr::term_manager& tm, const options& opts, utils::statistics& stats)
: solver("z3", tm, opts, stats)
{
  d_internal = new z3_internal(tm, opts);
}

z3::~z3() {
  delete d_internal;
}

void z3::add(expr::term_ref f, formula_class f_class) {
  TRACE("z3") << "z3[" << d_internal->instance() << "]: adding " << f << std::endl;
  d_internal->add(f, f_class);
}

solver::result z3::check() {
  TRACE("z3") << "z3[" << d_internal->instance() << "]: check()" << std::endl;
  return d_internal->check();
}

expr::model::ref z3::get_model() const {
  TRACE("z3") << "z3[" << d_internal->instance() << "]: get_model()" << std::endl;
  return d_internal->get_model(d_A_variables, d_T_variables, d_B_variables);
}

void z3::push() {
  TRACE("z3") << "z3[" << d_internal->instance() << "]: push()" << std::endl;
  d_internal->push();
}

void z3::pop() {
  TRACE("z3") << "z3[" << d_internal->instance() << "]: pop()" << std::endl;
  d_internal->pop();
}

void z3::add_variable(expr::term_ref var, variable_class f_class) {
  solver::add_variable(var, f_class);
  d_internal->add_variable(var, f_class);
}

void z3::gc() {
  d_internal->gc();
}

void z3::gc_collect(const expr::gc_relocator& gc_reloc) {
  solver::gc_collect(gc_reloc);
  d_internal->gc_collect(gc_reloc);
}

}
}

#endif
