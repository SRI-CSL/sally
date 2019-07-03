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

#ifdef WITH_YICES2

#ifndef __STDC_LIMIT_MACROS
#define __STDC_LIMIT_MACROS 1
#endif

#include <gmp.h>
#include <yices.h>
#include <vector>

#include "expr/term_manager.h"
#include "expr/model.h"
#include "smt/solver.h"

namespace sally {
namespace smt {

class yices2_term_cache;

class yices2_internal {

  /** The term manager */
  expr::term_manager& d_tm;

  /** Number of yices instances */
  static int s_instances;

  /** Yices boolean type */
  static type_t s_bool_type;

  /** Yices integer type */
  static type_t s_int_type;

  /** Yices real type */
  static type_t s_real_type;

  /** Yices context (dpllt) */
  context_t *d_ctx_dpllt;

  /** Yices context (dpllt) */
  context_t *d_ctx_mcsat;

  /** Is dpllt incomplete */
  bool d_dpllt_incomplete;

  /** Is mcsat incomplete */
  bool d_mcsat_incomplete;

  /** Remember incompleteness across push/pop */
  std::vector<bool> d_dpllt_incomplete_log;
  std::vector<bool> d_mcsat_incomplete_log;

  /** All assertions we have in context (strong)  */
  std::vector<expr::term_ref_strong> d_assertions;

  /** The assertion classes */
  std::vector<solver::formula_class> d_assertion_classes;

  /** The assertions size per push/pop */
  std::vector<size_t> d_assertions_size;

  /** A variables */
  std::vector<expr::term_ref> d_A_variables;
  std::set<expr::term_ref> d_A_variables_set;

  /** B variables */
  std::vector<expr::term_ref> d_B_variables;
  std::set<expr::term_ref> d_B_variables_set;

  /** T variables */
  std::vector<expr::term_ref> d_T_variables;
  std::set<expr::term_ref> d_T_variables_set;

  /** Term conversion cache */
  yices2_term_cache* d_conversion_cache;

  /** Bitvector 1 */
  expr::term_ref_strong d_bv1;

  /** Bitvector 0 */
  expr::term_ref_strong d_bv0;

  /** Last check return (dpllt) */
  smt_status_t d_last_check_status_dpllt;
  /** Last check return (mcsat) */
  smt_status_t d_last_check_status_mcsat;

  /** Yices config (dpllt) */
  ctx_config_t* d_config_dpllt;
  /** Yices config (mcsat) */
  ctx_config_t* d_config_mcsat;

  /** The instance */
  size_t d_instance;

  /** Print the EFSMT to output */
  void efsmt_to_stream(std::ostream& out, const term_vector_t* G_y, const term_t* assertions, size_t assertions_size,
      const std::vector<expr::term_ref>& exists_vars,
      const std::vector<expr::term_ref>& forall_vars_1,
      const std::vector<expr::term_ref>& forall_vars_2);

  /** Check the error */
  void check_error(int ret, const char* error_msg) const;

  /** Get the variables used in assertions */
  void get_variables(std::vector<expr::term_ref>& variables);

public:

  /** Construct an instance of yices with the given term manager and options */
  yices2_internal(expr::term_manager& tm, const options& opts);

  /** Destroy yices instance */
  ~yices2_internal();

  /** Get the yices version of the term */
  term_t to_yices2_term(expr::term_ref ref);

  /** Get the yices version of the type */
  type_t to_yices2_type(expr::term_ref ref);

  /** Get the sal version of the term */
  expr::term_ref to_term(term_t t);

  /** Make a term given yices operator and children */
  expr::term_ref mk_term(term_constructor_t constructor, const std::vector<expr::term_ref>& children);

  /** If Boolean convert to bitvector, otherwise keep. */
  expr::term_ref bool_term_to_bv(expr::term_ref t);

  /** Make a yices term with given operator and children */
  term_t mk_yices2_term(expr::term_op op, size_t n, term_t* children);

  /** Add an assertion to yices */
  void add(expr::term_ref ref, solver::formula_class f_class);

  /** Add a variable */
  void add_variable(expr::term_ref var, solver::variable_class f_class);

  /** Get the assertions into the set */
  void get_assertions(std::set<expr::term_ref>& out) const;

  /** Check satisfiability */
  solver::result check();

  /** Is the state consistent */
  bool is_consistent();

  /** Returns the model */
  expr::model::ref get_model();

  /** Returns yices model from sally model */
  model_t* get_yices_model(expr::model::ref m);

  /** Push the context */
  void push();

  /** Pop the context */
  void pop();

  /** Return the generalization */
  void generalize(smt::solver::generalization_type type, std::vector<expr::term_ref>& projection_out);

  /** Return the generalization */
  void generalize(smt::solver::generalization_type type, expr::model::ref, std::vector<expr::term_ref>& projection_out);

  /** Set the model hint */
  void set_hint(expr::model::ref m);

  /** Returns the instance id */
  size_t instance() const { return d_instance; }

  /** Term collection */
  void gc_collect(const expr::gc_relocator& gc_reloc);

  /** Collect garbage */
  void gc();

  /** Wrap yices_error_string cleanly */
  static std::string yices_error(void);
  

};


}
}

#endif
