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
 * Promote parameter variables to state variables.
 */
class promote_params_to_state: public transform {

  static factory::register_transform<promote_params_to_state> s_register;

public:

  promote_params_to_state(context* ctx, const transition_system* original);

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
  promote_params_to_state(const transition_system* original, context *ctx, std::string id, const state_type *st);
  
  ~promote_params_to_state();

  /* Create a new transition system and state formulas with the given
     id in the constructor (to be managed by the context) */
  void apply (const transition_system *ts,
	      const std::vector<const state_formula*>& queries,
	      transition_system*& new_ts,
	      std::vector<const state_formula*>& new_queries);

  std::string get_name() const {
    return "Promote non-state to state variables";
  }
  
  virtual size_t get_priority() const {
    return 5;
  }

private:

  // forward declaration
  class promote_nonstate_to_state_impl;
  promote_nonstate_to_state_impl *m_pImpl;
  
  typedef expr::term_manager::substitution_map substitution_map;

  /** Substitution map */
  substitution_map d_substitution_map;


};
  
}
}
}
