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

#ifdef WITH_DREAL

#include "smt/dreal/dreal_term.h"
#include "expr/term_manager.h"
#include "expr/term_map.h"
#include "expr/model.h"
#include "smt/solver.h"

#include <vector>

namespace sally {
namespace smt {

class dreal_term_cache;

class dreal_internal {

  /** The term manager */
  expr::term_manager& d_tm;

  /** Number of dreal instances */
  static size_t s_instances;

  /** The dreal context */
  ::dreal::Context *d_ctx;

  /** The bounded dreal context */
  ::dreal::Context *d_ctx_bounded;

  /** All assertions we have in context (strong)  */
  std::vector<expr::term_ref_strong> d_assertions;
  
  /** dreal assertions, for debug purposes */
  std::vector<::dreal::Formula> d_assertions_dreal;
  
  /** The assertions size per push/pop */
  std::vector<size_t> d_assertions_size;

  /** All variables */
  std::vector<expr::term_ref> d_variables;

  /** Dreal term conversion cache */
  dreal_term_cache* d_conversion_cache;

  /** Last check return */
  solver::result d_last_check_status;

  /** Last model dreal provided */
  expr::model::ref d_last_model;
  
  /** The dreal config */
  ::dreal::Config* d_config;

  /** The instance */
  size_t d_instance;

  /** Sally options */
  const options& d_options;

  /** Get variables used in assertions */
  void get_used_variables(std::vector<expr::term_ref>& variables) const;

  typedef expr::term_ref_map<expr::rational> term_to_rational_map;


  /** Construct Sally model from the simple model */
  expr::model::ref get_model_from_simple_model(const term_to_rational_map& simple_model);

  /**
   * Get model from dreal and put it into d_last_model. Returns true if
   * The model satisfies the assertions.
   */
  bool save_dreal_model(const ::dreal::Box& model);

  /** Check if the model is correct */
  bool check_model() const;

  /** Output solver assertions in smt2lib format*/
  void dreal_to_smtlib2(std::ostream& out);
  
  /** Extra assertions if needed */
  std::vector<dreal_term> d_extraAssertions;

 public:

  /** Construct an instance of dreal with the given term manager and options */
  dreal_internal(expr::term_manager& tm, const options& opts);

  /** Destroy dreal instance */
  ~dreal_internal();

  /* Get the dreal version of the term ref */
  dreal_term to_dreal_term(expr::term_ref ref);

  /** Get the sally version of the dreal t */
  expr::term_ref to_term(dreal_term t);

  /** Get the dreal version of the type */
  ::dreal::Variable::Type to_dreal_type(expr::term_ref ref);

  /** Make a dreal term with given operator and children */
  dreal_term mk_dreal_term(expr::term_op op, std::vector<dreal_term>& children);

  /** Add an assertion to dreal */
  void add(expr::term_ref ref, solver::formula_class f_class);

  /** Add a variable */
  void add_variable(expr::term_ref var, solver::variable_class f_class);

  /** Check satisfiability */
  solver::result check();

  /** Check satisfiability */
  solver::result check_relaxed();

  /** Returns the model */
  expr::model::ref get_model();

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
