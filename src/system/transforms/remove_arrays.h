#pragma once

#include "system/context.h"
#include "system/state_type.h"
#include "system/state_formula.h"
#include "system/transition_formula.h"

#include "transform.h"

#include <string>

namespace sally {
namespace system {
namespace transforms {
  
/** 
 * Reduce to formula to array reads only when the index domain is finit. This can
 * be done by:
 * - For equalities a = b, reduce to forall i. a[i] = b[i]
 * - For function application f(a), reduce to f'(a[0], ..., a[n])
 * - Push reads until they are on base arrays, for example
 *
 *   (ite c A B)[i] -> (ite c A[i] B[i])
 *   (write A i v)[k] -> (ite (= i k) v A[i])
 */
class remove_arrays: public transform {

  static factory::register_transform<remove_arrays> s_register;

  typedef expr::term_manager::substitution_map substitution_map;

  /** Main cache for rewrites */
  substitution_map d_substitution_map;

  /**
   * Main function that goes over the formula, identifies full-array
   * atoms, and decomposes them into individual reads.
   */
  expr::term_ref process(expr::term_ref f);

public:

  remove_arrays(context* ctx, const transition_system* original);

  /** Apply the transform to a state formula */
  state_formula* apply(const state_formula* f_state, direction D);

  /** Apply the transform to a transition formula */
  transition_formula* apply(const transition_formula* f_trans, direction D);

  /** Apply the transform to a model */
  expr::model::ref apply(expr::model::ref model, direction d);

  // Id is a fresh identifier managed by the context ctx so that new
  // state type, transition system, and state formula are associated
  // to Id. The constructor also creates the new state type from st
  // and it will be managed by the context.
  remove_arrays(const transition_system* original, context *ctx, std::string id, const state_type *st);
  
  ~remove_arrays();

  /* Create a new transition system and state formulas without arrays
     (if possible) with the given id in the constructor (to be managed
     by the context) */
  void apply (const transition_system *ts,
	      const std::vector<const state_formula*>& queries,
	      transition_system*& new_ts,
	      std::vector<const state_formula*>& new_queries);
  
  std::string get_name() const {
    return "Remove arrays";
  }

  virtual size_t get_priority() const {
    return 2;
  }

private:

  // forward declaration
  class remove_arrays_impl;
  remove_arrays_impl *m_pImpl;
  
};
  
}
}
}
