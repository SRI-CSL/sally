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

#pragma once

#ifdef WITH_Z3

// BD: we need to avoid redefining __STDC_LIMIT_MACROS
// otherwise compilation fails with Clang++ on the Mac
#ifndef __STDC_LIMIT_MACROS
#define __STDC_LIMIT_MACROS 1
#endif

#include <gmp.h>
#include <vector>

extern "C"
{
  #include <z3.h>
}

#include "expr/term_manager.h"
#include "smt/solver.h"

namespace sally {
namespace smt {

class z3_common;

class z3_internal {

  /** The term manager */
  expr::term_manager& d_tm;

  /** Number of yices instances */
  static int s_instances;

  /** The z3 context */
  Z3_context d_ctx;

  /** The z3 solver */
  Z3_solver d_solver;

  /** Parameters of the solvers */
  Z3_params d_params;

  /** All assertions we have in context (strong)  */
  std::vector<expr::term_ref_strong> d_assertions;

  /** The assertion classes */
  std::vector<solver::formula_class> d_assertion_classes;

  /** The assertions size per push/pop */
  std::vector<size_t> d_assertions_size;

  /** A variables */
  std::vector<expr::term_ref> d_A_variables;

  /** B variables */
  std::vector<expr::term_ref> d_B_variables;

  /** T variables */
  std::vector<expr::term_ref> d_T_variables;

  /** Term conversion cache */
  z3_common* d_conversion_cache;

  /** Bitvector 1 */
  expr::term_ref_strong d_bv1;

  /** Bitvector 0 */
  expr::term_ref_strong d_bv0;

  /** Last check return */
  Z3_lbool d_last_check_status;

  /** The instance */
  size_t d_instance;

public:

  /** Construct an instance of yices with the given temr manager and options */
  z3_internal(expr::term_manager& tm, const options& opts);

  /** Destroy yices instance */
  ~z3_internal();

  /** Get the yices version of the term */
  Z3_ast to_z3_term(expr::term_ref ref);

  /** Get the yices version of the type */
  Z3_sort to_z3_type(expr::term_ref ref);

  /** Get the sally version of the term */
  expr::term_ref to_term(Z3_ast t);

  /** Make a z3 term with given operator and children */
  Z3_ast mk_z3_term(expr::term_op op, size_t n, const std::vector<Z3_ast>& children);

  /** Make a term given z3 operator and children */
  expr::term_ref mk_term(Z3_decl_kind kind, const std::vector<expr::term_ref>& children);

  /** Add an assertion to yices */
  void add(expr::term_ref ref, solver::formula_class f_class);

  /** Add a variable */
  void add_variable(expr::term_ref var, solver::variable_class f_class);

  /** Get the assertions into the set */
  void get_assertions(std::set<expr::term_ref>& out) const;

  /** Check satisfiability */
  solver::result check();

  /** Returns the model */
  expr::model::ref get_model(const std::set<expr::term_ref>& x_variables, const std::set<expr::term_ref>& T_variables, const std::set<expr::term_ref>& y_variables);

  /** Push the context */
  void push();

  /** Pop the context */
  void pop();

  /** Returns the instance id */
  size_t instance() const { return d_instance; }

  /** Term collection */
  void gc_collect(const expr::gc_relocator& gc_reloc);

  /** Collect garbage */
  void gc();
};


}
}

#endif
