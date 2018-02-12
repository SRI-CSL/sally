#pragma once

#include "system/state_formula.h"
#include "system/transition_system.h"

#include <string>
#include <vector>

namespace sally {
namespace cmd {
namespace transforms {

/**
 * Generic transition system transformer class. It takes a transition system
 * and can transform formulas and models forward (and backward).
 */
class transform {

protected:

  /** The original transition system */
  const system::transition_system* d_original;

  /** The transformed transition system */
  system::transition_system* d_transformed;

public:
  
  /** Construct the transform that tranforms the given transition system */
  transform(const system::transition_system* original);

  /** Base class for a transform constructor */
  class constructor {
  public:
    virtual transform* mk_new(const system::transition_system* original) = 0;
    virtual ~constructor() {}
  };

  /** Constructor for a specific translate */
  template<typename T>
  class constructor_for : public constructor {
  public:
	transform* mk_new(const system::transition_system* original) {
	  return new T(original);
	}
  };

  /** Get the original transition system */
  const system::transition_system* get_original() const { return d_original; }

  /** Get the transformed transition system */
  const system::transition_system* get_transformed() const { return d_transformed; }

  /** Destructor */
  virtual ~transform() {}

  /** Direction of the transformation */
  enum direction {
	/** Tranform forward, from original to new */
    TRANSFORM_FORWARD,
	/** Transform backward, from new to original */
	TRANSFORM_BACKWARD
  };

  /** Apply the transform to a state formula */
  system::state_formula* apply(const system::state_formula* f_state, direction D);

  /** Apply the transform to a transition formula */
  system::transition_formula* apply(const system::transition_formula* f_trans, direction D);

  /** Apply the transform to a model */
  expr::model::ref apply(expr::model::ref model, direction d);

  /** Apply the transform */
  virtual void apply (const system::transition_system *ts,
		      const std::vector<const system::state_formula*>& queries,
		      system::transition_system*& new_ts,
		      std::vector<const system::state_formula*>& new_queries) = 0;
  
  /** Get the id to use for this transform */
  virtual std::string get_name() const = 0;

  /** The the priority of this transform (smaller goes first) */
  virtual size_t get_priority() const = 0;

};

/** Information for constructing a transformer by name */
struct transform_info {
  std::string id;
  size_t priority;
  transform::constructor* constructor;
  transform_info(): priority(0), constructor(0) {}
  transform_info(std::string id, size_t priority, transform::constructor* constructor)
  : id(id), priority(priority), constructor(constructor) {}
};

/**
 * Factory for creating SMT solvers.
 */
class factory {

  /** Map from transform IDs to info about them */
  typedef std::map<std::string, transform_info> transforms_info_map;

  /** Convenience so that we can have safe static initialization */
  struct info {
    transforms_info_map* m;
    transforms_info_map* get();
    ~info();
  };

  /** Map from id's to the info */
  static info s_info;

  friend class register_transform;

public:

  /** Convenience class for registering a transform */
  template<typename T>
  class register_transform {
    register_transform();
  public:
    register_transform(const char* id, size_t priority);
  };

  /** Get comma separated list of transforms */
  static
  std::string get_transforms_list();

  /** Get comma separated list of default transforms */
  static
  std::string get_default_transforms_list();

  /** Construct a transform by name, given a transition system to operate on */
  static
  transform* mk_transform(std::string id, const system::transition_system* original);

};

}
}
}
