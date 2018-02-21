#pragma once

#include "system/context.h"
#include "system/state_type.h"
#include "system/state_formula.h"
#include "system/transition_formula.h"

#include "transform.h"

#include <string>
#include <vector>

namespace sally {
namespace system {
namespace transforms {
  
/**
 * Remove enum types from transition systems and state formulas.
 */
class remove_enum_types: public transform {

  static factory::register_transform<remove_enum_types> s_register;

  typedef expr::term_manager::substitution_map substitution_map;

  /** Renaming of old variable to new variables */
  substitution_map d_substitution_map;

  typedef std::vector<expr::term_ref> term_ref_vec;

  /**
   * Replace the given enum type with a predicate subtype.
   */
  expr::term_ref enum_to_predicate_subtype(expr::term_ref t);

  /**
   * Take two vectors of variables and make a subsitution where types
   * differ, i.e. where we have ENUM -> REAL.
   */
  void process(const term_ref_vec& v1, const term_ref_vec& v2);

  /**
   * Takes a type variable (struct) and returns a new one without it.
   * The enum type is replaced with the real type.
   */
  expr::term_ref process(expr::term_ref type_var);

public:

  remove_enum_types(context* ctx, const transition_system* original);

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
  remove_enum_types(const transition_system* original, context *ctx, std::string id, const state_type *st);
  
  ~remove_enum_types();

  /* Create a new transition system and state formulas without enum
     types with the given id in the constructor (to be managed by the
     context) */
  void apply (const transition_system *ts,
	      const std::vector<const state_formula*>& queries,
	      transition_system*& new_ts,
	      std::vector<const state_formula*>& new_queries);

  std::string get_name() const {
    return "Remove enumeration types";
  }
  
  virtual size_t get_priority() const {
    return 3;
  }

private:

  // forward declaration
  class remove_enum_types_impl;
  remove_enum_types_impl *m_pImpl;
  
};
  
}
}
}
