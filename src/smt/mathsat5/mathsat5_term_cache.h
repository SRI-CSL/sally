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

#ifdef WITH_MATHSAT5

#include <map>
#include <vector>
#include <mathsat.h>
#include "expr/term_map.h"

#include "expr/term_manager.h"
#include "expr/gc_participant.h"

namespace sally {
namespace smt {

/** Yices term hash. */
struct mathsat5_hasher {
  size_t operator()(msat_term value) const { return msat_term_id(value); }
};

/** Equality checks */
struct mathsat5_eq {
  bool operator() (const msat_term& t1, const msat_term& t2) const {
    return msat_term_id(t1) == msat_term_id(t2);
  }
};

class mathsat5_term_cache : public expr::gc_participant {

  /** The term manager this cache is using */
  expr::term_manager& d_tm;

  /** Mathsat config */
  msat_config d_msat_cfg;

  /** Mathsat evnironment */
  msat_env d_msat_env;

  typedef expr::term_ref_map<msat_term> term_to_msat_cache;
  typedef expr::hash_map_to_term_ref<msat_term, mathsat5_hasher, mathsat5_eq> msat_to_term_cache;

  /** The map from terms to yices terms */
  term_to_msat_cache d_term_to_msat_cache;

  /** The map from yices terms to SAL terms */
  msat_to_term_cache d_msat_to_term_cache;

  bool d_cache_is_clean;

  /** Vector of permanent stuff (such as variables) that doesn't go away with gc */
  std::vector<expr::term_ref> d_permanent_terms;

  /** Vector of permanent stuff (such as variables) that doesn't go away with gc */
  std::vector<msat_term> d_permanent_terms_msat;

  class tm_to_cache_map {
  public:
    typedef std::map<size_t, mathsat5_term_cache*> map_type;
    map_type map;
    ~tm_to_cache_map();
    void clear();
  };

  /** Map from term managers to their term caches */
  static
  tm_to_cache_map s_tm_to_cache_map;

public:

  /** Create a new cache */
  mathsat5_term_cache(expr::term_manager& tm);

  /** Remove the cache */
  ~mathsat5_term_cache();

  /** Set the term cache from t -> t_msat. */
  void set_term_cache(expr::term_ref t, msat_term t_msat);

  /** Set the term cache from t_msat -> t. */
  void set_term_cache(msat_term t_msat, expr::term_ref t);

  /** Returns the mathsat5 term associated with t, or NULL_TERM otherwise */
  msat_term get_term_cache(expr::term_ref t) const;

  /** Returns our term representative for the msahsat5 term t or null otherwise */
  expr::term_ref get_term_cache(msat_term t) const;

  /** Get a cache associated with tm */
  static
  mathsat5_term_cache* get_cache(expr::term_manager& tm);

  /** Clear all caches */
  static
  void clear_all();

  /** Clear the cache */
  void clear();

  /** Collect terms */
  void gc_collect(const expr::gc_relocator& gc_reloc);

  /** Collect the cache, leaving only the variables */
  void gc();

  /** Get the mathsat5 environment that keeps the terms */
  msat_env get_msat_env() const;

};

}
}

#endif
