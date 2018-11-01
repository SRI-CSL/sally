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

/*
 * BD: fixed a compilation problem.
 *
 * The __STDC_LIMIT_MACROS must be defined before 
 *
 *   #include <boost/unordered_map.hpp>
 *
 * otherwise it has no effect (because the boost file indirectly
 * includes <stdint.h>).
 */
#ifndef __STDC_LIMIT_MACROS
#define __STDC_LIMIT_MACROS 1
#endif

#include <map>
#include <vector>

#include "expr/term_manager.h"
#include "expr/gc_participant.h"
#include "expr/term_map.h"
#include "smt/dreal/dreal_internal.h"
#include "smt/dreal/dreal_term.h"

namespace sally {
namespace smt {
  
class dreal_term_cache : public expr::gc_participant {

  /** The term manager this cache is using */
  expr::term_manager& d_tm;

  typedef expr::term_ref_map<dreal_term> term_to_dreal_cache;
  typedef expr::hash_map_to_term_ref<dreal_term, dreal_hasher> dreal_to_term_cache; 

  /** The map from terms to dreal terms */
  term_to_dreal_cache d_term_to_dreal_cache;

  /** The map from dreal terms to SAL terms */
  dreal_to_term_cache d_dreal_to_term_cache;

  bool d_cache_is_clean;

  /** Vector of all permanent terms (such as variables) to stay beyond gc */
  std::vector<expr::term_ref> d_permanent_terms;

  class tm_to_cache_map {
  public:
    typedef std::map<size_t, dreal_term_cache*> map_type;
    map_type map;
    ~tm_to_cache_map();
  };

  /** Map from term managers to their term caches */
  static tm_to_cache_map s_tm_to_cache_map;

public:

  /** Create a new cache */
  dreal_term_cache(expr::term_manager& tm);

  /** Set the term cache from t -> t_dreal. */
  void set_term_cache(expr::term_ref t, dreal_term t_dreal);

  /** Set the term cache from t_dreal -> t. */
  void set_term_cache(dreal_term t_dreal, expr::term_ref t);

  /** Returns the dreal term associated with t, otherwise NULL_TERM*/
  dreal_term get_term_cache(expr::term_ref t) const;

  /** Returns our term representative for the dreal term t or null otherwise */
  expr::term_ref get_term_cache(dreal_term t) const;

  /** Get a cache associated with tm */
  static
  dreal_term_cache* get_cache(expr::term_manager& tm);

  /** Clear the cache */
  void clear();

  /** Term collection */
  void gc_collect(const expr::gc_relocator& gc_reloc);

  /** Collect the cache, leaving only the variables */
  void gc();
};

}
}

#endif
