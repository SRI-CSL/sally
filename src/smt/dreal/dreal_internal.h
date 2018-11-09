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
  static int s_instances;

  /** The dreal context */
  ::dreal::Context *d_ctx;

  /** All assertions we have in context (strong)  */
  std::vector<expr::term_ref_strong> d_assertions;

  /** Free variables from d_assertions */
  std::set<::dreal::Variable> d_assertion_vars;
  
  /** dreal assertions, for debug purposes */
  std::vector<::dreal::Formula> d_assertions_dreal;
  
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

  /** Dreal term conversion cache */
  dreal_term_cache* d_conversion_cache;

  /** Last check return */
  solver::result d_last_check_status;
    
  /** Last dreal model */
  typedef expr::term_ref_map<double> dreal_model_t;  
  dreal_model_t d_last_model;
  
  /** The dreal config */
  ::dreal::Config* d_config;

  /** The instance */
  size_t d_instance;

  /** Return true if a dreal model was extracted. If yes, the model is
      stored in d_last_model */
  bool get_dreal_model(const ::dreal::Box& model);

  /** Output solver assertions in smt2lib format*/
  void dreal_to_smtlib2(std::ostream& out);
  
 public:

  /** Construct an instance of dreal with the given temr manager and options */
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
