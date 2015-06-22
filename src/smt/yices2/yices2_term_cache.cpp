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
#ifdef WITH_YICES2

#include "smt/yices2/yices2_term_cache.h"
#include "expr/gc_relocator.h"

#include <iomanip>
#include <iostream>
#include <fstream>

#define unused_var(x) { (void)x; }

namespace sally {
namespace smt {

yices2_term_cache::yices2_term_cache(expr::term_manager& tm)
: gc_participant(tm)
, d_tm(tm)
, d_cache_is_clean(true)
{
}

yices2_term_cache::tm_to_cache_map yices2_term_cache::s_tm_to_cache_map;

void yices2_term_cache::set_term_cache(expr::term_ref t, term_t t_yices) {
  bool added = false;
  if (d_term_to_yices_cache.find(t) == d_term_to_yices_cache.end()) {
    d_term_to_yices_cache[t] = t_yices;
    added = true;
  }
  if (d_yices_to_term_cache.find(t_yices) == d_yices_to_term_cache.end()) {
    d_yices_to_term_cache[t_yices] = t;
    added = true;
  }
  unused_var(added);
  assert(added);
  // If a variable, remember it
  if (d_tm.term_of(t).op() == expr::VARIABLE) {
    d_permanent_terms.push_back(t);
    d_permanent_terms_yices.push_back(t_yices);
  } else {
    // Mark cache as dirty
    d_cache_is_clean = false;
  }

  // If enabled, check the term transformations by producing a series of
  // smt2 queries. To check run the contrib/smt2_to_yices.sh script and then
  // run on yices.
  if (output::trace_tag_is_enabled("yices2::terms")) {
    static size_t k = 0;
    std::stringstream ss;
    ss << "yices2_term_query_" << std::setfill('0') << std::setw(5) << k++ << ".smt2";
    std::ofstream query(ss.str().c_str());
    output::set_term_manager(query, &d_tm);
    output::set_output_language(query, output::MCMT);

    // Prelude
    // Get the term variables
    std::vector<expr::term_ref> vars;
    d_tm.get_variables(t, vars);
    for (size_t i = 0; i < vars.size(); ++ i) {
      query << "(declare-fun " << vars[i] << " () " << d_tm.type_of(vars[i]) << ")" << std::endl;
    }

    // Check the representation
    char* repr = yices_term_to_string(t_yices, UINT32_MAX, UINT32_MAX, 0);
    query << "(assert (not (= " << repr << " " << t << ")))" << std::endl;
    yices_free_string(repr);

    query << "(check-sat)" << std::endl;
    d_tm.set_name_transformer(0);
  }
}

term_t yices2_term_cache::get_term_cache(expr::term_ref t) const {
  term_to_yices_cache::const_iterator find = d_term_to_yices_cache.find(t);
  if (find != d_term_to_yices_cache.end()) {
    return find->second;
  } else {
    return NULL_TERM;
  }
}

expr::term_ref yices2_term_cache::get_term_cache(term_t t) const {
  yices_to_term_cache::const_iterator find = d_yices_to_term_cache.find(t);
  if (find != d_yices_to_term_cache.end()) {
    return find->second;
  } else {
    return expr::term_ref();
  }
}

void yices2_term_cache::clear() {
  d_cache_is_clean = true;
  d_term_to_yices_cache.clear();
  d_term_to_yices_cache.clear();
  d_permanent_terms.clear();
  d_permanent_terms_yices.clear();
}

yices2_term_cache* yices2_term_cache::get_cache(expr::term_manager& tm) {

  yices2_term_cache* cache = 0;

  // Try to find an existing one
  tm_to_cache_map::const_iterator find = s_tm_to_cache_map.find(&tm);
  if (find != s_tm_to_cache_map.end()) {
    cache = find->second;
  } else {
    cache = new yices2_term_cache(tm);
  }

  return cache;
}

void yices2_term_cache::gc() {
  if (!d_cache_is_clean) {

    // Terms we'd like to keep (just variables)
    term_t* terms_to_keep = new term_t[d_permanent_terms.size()];

    // Create a new cache that contains just the variables
    d_term_to_yices_cache.clear();
    d_yices_to_term_cache.clear();
    for (size_t i = 0; i < d_permanent_terms.size(); ++ i) {
      d_term_to_yices_cache[d_permanent_terms[i]] = d_permanent_terms_yices[i];
      d_yices_to_term_cache[d_permanent_terms_yices[i]] = d_permanent_terms[i];
      terms_to_keep[i] = d_permanent_terms_yices[i];
    }

    // Collect the garbage
    yices_garbage_collect(terms_to_keep, d_permanent_terms.size(), NULL, 0, true);
    delete terms_to_keep;

    // We're clean now
    d_cache_is_clean = true;
  }
}

void yices2_term_cache::gc_collect(const expr::gc_relocator& gc_reloc) {
  d_term_to_yices_cache.reloc(gc_reloc);
  d_yices_to_term_cache.reloc(gc_reloc);
  gc_reloc.reloc(d_permanent_terms);
}

}
}

#endif
