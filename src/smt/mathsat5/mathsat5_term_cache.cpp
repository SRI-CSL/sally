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

#ifdef WITH_MATHSAT5

#include <iostream>
#include <fstream>
#include <iomanip>

#include "smt/solver.h"
#include "smt/mathsat5/mathsat5_term_cache.h"

#include "expr/gc_relocator.h"

#define unused_var(x) { (void)x; }

namespace sally {
namespace smt {

mathsat5_term_cache::mathsat5_term_cache(expr::term_manager& tm)
: gc_participant(tm)
, d_tm(tm)
, d_cache_is_clean(true)
{
  d_msat_cfg = msat_create_config();
  if (MSAT_ERROR_CONFIG(d_msat_cfg)) {
    throw exception("Error in Mathsat5 initialization");
  }
  d_msat_env = msat_create_env(d_msat_cfg);
  if (MSAT_ERROR_ENV(d_msat_env)) {
    throw exception("Error in MathSAT5 initialization");
  }
}

mathsat5_term_cache::~mathsat5_term_cache() {
  // Remove the master
  msat_destroy_env(d_msat_env);
  msat_destroy_config(d_msat_cfg);
}

mathsat5_term_cache::tm_to_cache_map mathsat5_term_cache::s_tm_to_cache_map;

void mathsat5_term_cache::set_term_cache(expr::term_ref t, msat_term t_msat) {
  // Due to normalization in SMT solvers, two terms t1 and t2 can map to the
  // same term t_msat. We can't map t_msat to both t1 and t2, so we only keep
  // one
  bool added = false;
  if (d_term_to_msat_cache.find(t) == d_term_to_msat_cache.end()) {
    d_term_to_msat_cache[t] = t_msat;
    added = true;
  }
  if (d_msat_to_term_cache.find(t_msat) == d_msat_to_term_cache.end()) {
    d_msat_to_term_cache[t_msat] = t;
    added = true;
  }
  unused_var(added);
  assert(added);
  // If a variable, remember it
  if (d_tm.term_of(t).op() == expr::VARIABLE) {
    d_permanent_terms.push_back(t);
    d_permanent_terms_msat.push_back(t_msat);
  } else {
    // Mark cache as dirty
    d_cache_is_clean = false;
  }

  // If enabled, check the term transformations by producing a series of
  // smt queries
  if (output::trace_tag_is_enabled("mathsat5::terms")) {
    static size_t k = 0;
    std::stringstream ss;
    ss << "mathsat5_term_query_" << std::setfill('0') << std::setw(5) << k++ << ".smt2";
    smt2_name_transformer name_transformer;
    d_tm.set_name_transformer(&name_transformer);
    std::ofstream query(ss.str().c_str());
    output::set_term_manager(query, &d_tm);
    output::set_output_language(query, output::MCMT);

    // Prelude
    for (size_t i = 0; i < d_permanent_terms.size(); ++ i) {
      query << "(declare-fun " << d_permanent_terms[i] << " () " << d_tm.type_of(d_permanent_terms[i]) << ")" << std::endl;
    }

    // Check the representation
    char* repr = msat_to_smtlib2_term(d_msat_env, t_msat);
    query << "(assert (not (= " << repr << " " << t << ")))" << std::endl;
    msat_free(repr);

    query << "(check-sat)" << std::endl;
    d_tm.set_name_transformer(0);
  }
}

msat_term mathsat5_term_cache::get_term_cache(expr::term_ref t) const {
  term_to_msat_cache::const_iterator find = d_term_to_msat_cache.find(t);
  if (find != d_term_to_msat_cache.end()) {
    return find->second;
  } else {
    msat_term error;
    MSAT_MAKE_ERROR_TERM(error);
    return error;
  }
}

expr::term_ref mathsat5_term_cache::get_term_cache(msat_term t) const {
  msat_to_term_cache::const_iterator find = d_msat_to_term_cache.find(t);
  if (find != d_msat_to_term_cache.end()) {
    return find->second;
  } else {
    return expr::term_ref();
  }
}

msat_env mathsat5_term_cache::get_msat_env() const {
  return d_msat_env;
}

void mathsat5_term_cache::clear() {
  d_cache_is_clean = true;
  d_msat_to_term_cache.clear();
  d_term_to_msat_cache.clear();
  d_permanent_terms.clear();
  d_permanent_terms_msat.clear();
}

mathsat5_term_cache* mathsat5_term_cache::get_cache(expr::term_manager& tm) {

  mathsat5_term_cache* cache = 0;

  // Try to find an existing one
  tm_to_cache_map::const_iterator find = s_tm_to_cache_map.find(&tm);
  if (find != s_tm_to_cache_map.end()) {
    cache = find->second;
  } else {
    cache = new mathsat5_term_cache(tm);
  }

  return cache;
}


void mathsat5_term_cache::gc() {
  if (!d_cache_is_clean) {

    // Terms we'd like to keep (just variables)
    msat_term* terms_to_keep = new msat_term[d_permanent_terms.size()];

    // Create a new cache that contains just the variables
    d_term_to_msat_cache.clear();
    d_msat_to_term_cache.clear();
    for (size_t i = 0; i < d_permanent_terms.size(); ++ i) {
      d_term_to_msat_cache[d_permanent_terms[i]] = d_permanent_terms_msat[i];
      d_msat_to_term_cache[d_permanent_terms_msat[i]] = d_permanent_terms[i];
      terms_to_keep[i] = d_permanent_terms_msat[i];
    }

    // Collect the garbage
    msat_gc_env(d_msat_env, terms_to_keep, d_permanent_terms.size());
    delete terms_to_keep;

    // We're clean now
    d_cache_is_clean = true;
  }
}

void mathsat5_term_cache::gc_collect(const expr::gc_relocator& gc_reloc) {
  d_term_to_msat_cache.reloc(gc_reloc);
  d_msat_to_term_cache.reloc(gc_reloc);
  gc_reloc.reloc(d_permanent_terms);
}

}
}

#endif
