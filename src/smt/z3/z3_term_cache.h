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

#ifdef WITH_Z3

#include <map>
#include <vector>

#include "expr/term_manager.h"
#include "expr/gc_participant.h"
#include "expr/term_map.h"
#include "smt/z3/z3_internal.h"

namespace sally {
namespace smt {

/** Yices term hash. */
struct z3_hasher {
  Z3_context ctx;
  size_t operator()(Z3_ast value) const { return Z3_get_ast_hash(ctx, value); }
};

class z3_term_cache : public expr::gc_participant {

  /** The term manager this cache is using */
  expr::term_manager& d_tm;

  /** z3 context */
  Z3_context d_ctx;

  typedef expr::term_ref_map<Z3_ast> term_to_z3_cache;
  typedef expr::hash_map_to_term_ref<Z3_ast, z3_hasher> z3_to_term_cache;

  /** Hasher for z3 terms */
  z3_hasher d_hasher;

  /** The map from terms to z3 terms */
  term_to_z3_cache d_term_to_z3_cache;

  /** The map from z3 terms to SAL terms */
  z3_to_term_cache d_z3_to_term_cache;

  bool d_cache_is_clean;

  /** Vector of all permanent terms (such as variables) to stay beyond gc */
  std::vector<expr::term_ref> d_permanent_terms;

  /** Vector of all permanent terms (such as variables) to stay beyond gc */
  std::vector<Z3_ast> d_permanent_terms_z3;

  class tm_to_cache_map {
  public:
    typedef std::map<size_t, z3_term_cache*> map_type;
    map_type map;
    ~tm_to_cache_map();
  };

  /** Map from term managers to their term caches */
  static tm_to_cache_map s_tm_to_cache_map;

public:

  /** Create a new cache */
  z3_term_cache(expr::term_manager& tm);

  /** Delete the term cache */
  ~z3_term_cache();

  /** Get the z3 context */
  Z3_context get_context() const {
    return d_ctx;
  }

  /** Set the term cache from t -> t_z3. */
  void set_term_cache(expr::term_ref t, Z3_ast t_z3);

  /** Set the term cache from t_z3 -> t. */
  void set_term_cache(Z3_ast t_z3, expr::term_ref t);

  /** Returns the z3 term associated with t, or NULL_TERM otherwise */
  Z3_ast get_term_cache(expr::term_ref t) const;

  /** Returns our term representative for the z3 term t or null otherwise */
  expr::term_ref get_term_cache(Z3_ast t) const;

  /** Get a cache associated with tm */
  static
  z3_term_cache* get_cache(expr::term_manager& tm);

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
