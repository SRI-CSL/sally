#pragma once

#include "system/context.h"
#include "system/state_type.h"
#include "system/state_formula.h"
#include "system/transition_formula.h"
#include "transform.h"

#include <boost/program_options/options_description.hpp>

#include <string>
#include <vector>

namespace sally {
namespace system {
namespace transforms {

/**
 * Transformations to simplify the syntax of the transitions system
 * and state formulas so that solvers can handle them.
 */
class preprocessor {

  /** The context we're operating under */
  context* d_ctx;

  /** Original transition system */
  const transition_system* d_original;

  /** List of transforms, in order */
  typedef std::vector<transform*> transforms_vector;
  transforms_vector d_transforms;

public:
  
  /**
   * Create the preprocessor for the given transition system. It will create
   * a pre-processed system in the context with the given id.
   */
  preprocessor(context* ctx, std::string system_id, std::string preprocessed_id);

  /**
   * Destroy the preprocess and all the transforms.
   */
  ~preprocessor();

  /** Run the pre-processor on the given state formula. */
  state_formula* apply(const state_formula* sf, transform::direction D);

  /** Run the pre-processor on the given transition formula. */
  transition_formula* apply(const transition_formula* sf, transform::direction D);

  /** Run the pre-processor on the given model. */
  expr::model::ref apply(expr::model::ref m, transform::direction D);

  /**
   * Perform several transformations on the given ts and queries. The
   * transformation is functional so it produces a new transition system and
   * a new vector of queries. **/
  void run(std::string id,
	   const transition_system* ts,
	   const std::vector<const state_formula*>& queries,
	   transition_system*& new_ts,
	   std::vector<const state_formula*>& new_queries);


  /** Setup the options */
  static
  void setup_options(boost::program_options::options_description& options);
  
private:
  
  void run_transform(transform* tr,
		     const transition_system* ts,
		     const std::vector<const state_formula*>& queries,
		     transition_system*& new_ts,
		     std::vector<const state_formula*>& new_queries);
};

}}} // End namespace



