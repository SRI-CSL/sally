/*
 * yices2_term_cache.h
 *
 *  Created on: Apr 8, 2015
 *      Author: dejan
 */

#pragma once

#ifdef WITH_YICES2

#include <map>
#include <vector>
#include <boost/unordered_map.hpp>

#include "expr/term_manager.h"
#include "smt/yices2/yices2_internal.h"

namespace sally {
namespace smt {

/** Yices term hash. */
struct yices_hasher {
  size_t operator()(term_t value) const { return value; }
};

class yices2_term_cache {

  /** The term manager this cache is using */
  expr::term_manager& d_tm;

  typedef boost::unordered_map<expr::term_ref, term_t, expr::term_ref_hasher> term_to_yices_cache;
  typedef boost::unordered_map<term_t, expr::term_ref, yices_hasher> yices_to_term_cache;

  /** The map from terms to yices terms */
  term_to_yices_cache d_term_to_yices_cache;

  /** The map from yices terms to SAL terms */
  yices_to_term_cache d_yices_to_term_cache;

  bool d_cache_is_clean;

  /** Set of all yices instances */
  std::set<const yices2_internal*> d_all_yices_instances;

  typedef std::map<expr::term_manager*, yices2_term_cache*> tm_to_cache_map;

  /** Map from term managers to their term caches */
  static
  std::map<expr::term_manager*, yices2_term_cache*> s_tm_to_cache_map;

  /** Clear the cache */
  void clear();

public:

  /** Create a new cache */
  yices2_term_cache(expr::term_manager& tm);

  /**
   * Set the term cache from t -> t_yices. If t_yices doesn't exist in the
   * cache already, add the map t_yices -> t.
   */
  void set_term_cache(expr::term_ref t, term_t t_yices);

  /** Returns the yices term associated with t, or NULL_TERM otherwise */
  term_t get_term_cache(expr::term_ref t) const;

  /** Returns our term representative for the yices term t or null otherwise */
  expr::term_ref get_term_cache(term_t t) const;

  /** Get a cache associated with tm and attach to it */
  static
  yices2_term_cache* attach_to_cache(expr::term_manager& tm, const yices2_internal* instance);

  /** Detach the instance from the cache */
  void detach_from_cache(const yices2_internal* instance);

  /** Collect the cache */
  void gc();
};

}
}

#endif
