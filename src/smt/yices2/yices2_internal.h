/*
 * yices2_internal.h
 *
 *  Created on: Apr 8, 2015
 *      Author: dejan
 */

#pragma once

#ifdef WITH_YICES2

#define __STDC_LIMIT_MACROS 1

#include <gmp.h>
#include <yices.h>
#include <vector>

#include "expr/term_manager.h"
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

  /** The yices context */
  context_t *d_ctx;

  /** All assertions we have in context (strong)  */
  std::vector<expr::term_ref_strong> d_assertions;

  /** The assertion classes */
  std::vector<solver::formula_class> d_assertion_classes;

  /** The assertions size per push/pop */
  std::vector<size_t> d_assertions_size;

  /** All variables */
  std::vector<expr::term_ref> d_variables;

  /** Term conversion cache */
  yices2_term_cache* d_conversion_cache;

  /** Bitvector 1 */
  expr::term_ref_strong d_bv1;

  /** Bitvector 0 */
  expr::term_ref_strong d_bv0;

  /** Last check return */
  smt_status_t d_last_check_status;

  /** The yices config */
  ctx_config_t* d_config;

  /** The instance */
  size_t d_instance;

public:

  /** Construct an instance of yices with the given temr manager and options */
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

  /** Make a yices term with given operator and children */
  term_t mk_yices2_term(expr::term_op op, size_t n, term_t* children);

  /** Add an assertion to yices */
  void add(expr::term_ref ref, solver::formula_class f_class);

  /** Add an x variable */
  void add_x_variable(expr::term_ref x_var);

  /** Add a y variable */
  void add_y_variable(expr::term_ref y_var);

  /** Get the assertions into the set */
  void get_assertions(std::set<expr::term_ref>& out) const;

  /** Check satisfiability */
  solver::result check();

  /** Returns the model */
  void get_model(expr::model& m, const std::set<expr::term_ref>& x_variables, const std::set<expr::term_ref>& y_variables);

  /** Push the context */
  void push();

  /** Pop the context */
  void pop();

  /** Return the generalization */
  void generalize(smt::solver::generalization_type type, const std::set<expr::term_ref>& to_eliminate, std::vector<expr::term_ref>& projection_out);

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
