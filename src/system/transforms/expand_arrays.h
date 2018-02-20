#pragma once

#include "expr/term_manager.h"

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
 * Expand arrays from transition systems and state formulas. The
 * expansion consists of removing quantifiers, array lambda terms and
 * array variables involved in equalities. As a result of this
 * expansion, all array variables should appear only as arguments of
 * array read and write terms.  The expansion is only possible if the
 * array size is statically known.
 *
 * Note: an array is not expanded if it appears as an argument to a
 * function application term.
 **/
class expand_arrays: public transform {

  static factory::register_transform<expand_arrays> s_register;

  /** Expands arrays in a given term */
  expr::term_ref rewrite(expr::term_ref t);

  /** Keep substitution map */
  expr::term_manager::substitution_map d_subst_map;

public:

  expand_arrays(context* ctx, const transition_system* original);

  /** Apply the transform to a state formula */
  state_formula* apply(const state_formula* f_state, direction D);

  /** Apply the transform to a transition formula */
  transition_formula* apply(const transition_formula* f_trans, direction D);

  /** Apply the transform to a model */
  expr::model::ref apply(expr::model::ref model, direction d);

  expand_arrays(const transition_system* original, context *ctx, std::string id);

  /* Create a new transition system and state formulas with the given
     id (to be managed by the context) */
  void apply (const transition_system *ts,
	      const std::vector<const state_formula*>& queries,
	      transition_system*& new_ts,
	      std::vector<const state_formula*>& new_queries);

  std::string get_name() const {
    return "Expand arrays";
  }
  
  virtual size_t get_priority() const {
    return 1;
  }

private:
  
  std::string d_id;
};
  
}
}
}
