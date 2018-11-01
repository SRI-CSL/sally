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

#ifdef WITH_DREAL

#include <iostream>
#include <fstream>
#include <iomanip>

#include "expr/term.h"
#include "expr/term_manager.h"
#include "expr/rational.h"
#include "smt/dreal/dreal.h"
#include "smt/dreal/dreal_internal.h"
#include "utils/trace.h"

#define unused_var(x) { (void) x; }

namespace sally {
namespace smt {

dreal::dreal(expr::term_manager& tm, const options& opts, utils::statistics& stats)
: solver("dreal", tm, opts, stats)
{
  d_internal = new dreal_internal(tm, opts);
}

dreal::~dreal() {
  delete d_internal;
}

void dreal::add(expr::term_ref f, formula_class f_class) {
  TRACE("dreal") << "dreal[" << d_internal->instance() << "]: adding " << f << std::endl;
  d_internal->add(f, f_class);
}

solver::result dreal::check() {
  TRACE("dreal") << "dreal[" << d_internal->instance() << "]: check()" << std::endl;
  return d_internal->check();
}

expr::model::ref dreal::get_model() const {
  TRACE("dreal") << "dreal[" << d_internal->instance() << "]: get_model()" << std::endl;
  return d_internal->get_model();
}

void dreal::push() {
  TRACE("dreal") << "dreal[" << d_internal->instance() << "]: push()" << std::endl;
  d_internal->push();
}

void dreal::pop() {
  TRACE("dreal") << "dreal[" << d_internal->instance() << "]: pop()" << std::endl;
  d_internal->pop();
}

void dreal::add_variable(expr::term_ref var, variable_class f_class) {
  solver::add_variable(var, f_class);
  d_internal->add_variable(var, f_class);
}

void dreal::gc() {
  d_internal->gc();
}

void dreal::gc_collect(const expr::gc_relocator& gc_reloc) {
  solver::gc_collect(gc_reloc);
  d_internal->gc_collect(gc_reloc);
}

}
}

#endif
