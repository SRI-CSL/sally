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
#ifdef WITH_DREAL

#include "smt/dreal/dreal_term_cache.h"
#include "expr/gc_relocator.h"

#include <iomanip>
#include <iostream>
#include <fstream>

//#define unused_var(x) { (void)x; }

using namespace dreal;

namespace sally {
namespace smt {

dreal_term_cache::dreal_term_cache(expr::term_manager& tm)
: gc_participant(tm, false)
, d_tm(tm)
, d_cache_is_clean(true)
{
}

dreal_term_cache::tm_to_cache_map dreal_term_cache::s_tm_to_cache_map;

void dreal_term_cache::set_term_cache(expr::term_ref t, dreal_term t_dreal) {
  assert (d_term_to_dreal_cache.find(t) == d_term_to_dreal_cache.end());
  d_term_to_dreal_cache[t] = t_dreal;
  // If a variable, remember it
  if (d_tm.term_of(t).op() == expr::VARIABLE) {
    d_permanent_terms.push_back(t);
    d_dreal_to_term_cache[t_dreal] = t;
  } else {
    // Mark cache as dirty
    d_cache_is_clean = false;
  }

  // If enabled, check the term transformations by producing a series of
  // smt2 queries. 
  if (output::trace_tag_is_enabled("dreal::terms")) {
    static size_t k = 0;
    std::stringstream ss;
    ss << "dreal_term_query_" << std::setfill('0') << std::setw(5) << k++ << ".smt2";
    std::ofstream query(ss.str().c_str());
    output::set_term_manager(query, &d_tm);
    output::set_output_language(query, output::MCMT);

    // Prelude
    // Get the term variables
    std::vector<expr::term_ref> vars;
    d_tm.get_variables(t, vars);
    for (size_t i = 0; i < vars.size(); ++ i) {
      query << "(declare-fun " << vars[i] << " () " << d_tm.type_of(vars[i]) << ")"
	    << std::endl;
    }

    // Check the representation
    std::string repr = t_dreal.to_smtlib2();
    query << "(assert (not (= " << repr << " " << t << ")))" << std::endl;

    query << "(check-sat)" << std::endl;
    d_tm.set_name_transformer(0);
  }
}

void dreal_term_cache::set_term_cache(dreal_term t_dreal, expr::term_ref t) {
  assert(d_dreal_to_term_cache.find(t_dreal) == d_dreal_to_term_cache.end());
  d_dreal_to_term_cache[t_dreal] = t;
  // If a variable, remember it
  if (d_tm.term_of(t).op() == expr::VARIABLE) {
    d_permanent_terms.push_back(t);
    d_term_to_dreal_cache[t] = t_dreal;
  } else {
    // Mark cache as dirty
    d_cache_is_clean = false;
  }

  // If enabled, check the term transformations by producing a series of
  // smt2 queries. 
  if (output::trace_tag_is_enabled("dreal::terms")) {
    static size_t k = 0;
    std::stringstream ss;
    ss << "dreal_term_query_" << std::setfill('0') << std::setw(5) << k++ << ".smt2";
    std::ofstream query(ss.str().c_str());
    output::set_term_manager(query, &d_tm);
    output::set_output_language(query, output::MCMT);

    // Prelude
    // Get the term variables
    std::vector<expr::term_ref> vars;
    d_tm.get_variables(t, vars);
    for (size_t i = 0; i < vars.size(); ++ i) {
      query << "(declare-fun " << vars[i] << " () " << d_tm.type_of(vars[i]) << ")"
	    << std::endl;
    }

    // Check the representation
    std::string repr = t_dreal.to_smtlib2();
    query << "(assert (not (= " << repr << " " << t << ")))" << std::endl;

    query << "(check-sat)" << std::endl;
    d_tm.set_name_transformer(0);
  }
}


dreal_term dreal_term_cache::get_term_cache(expr::term_ref t) const {
  term_to_dreal_cache::const_iterator find = d_term_to_dreal_cache.find(t);
  if (find != d_term_to_dreal_cache.end()) {
    return find->second;
  } else {
    return dreal_term();
  }
}

expr::term_ref dreal_term_cache::get_term_cache(dreal_term t) const {
  dreal_to_term_cache::const_iterator find = d_dreal_to_term_cache.find(t);
  if (find != d_dreal_to_term_cache.end()) {
    return find->second;
  } else {
    return expr::term_ref();
  }
}

void dreal_term_cache::clear() {
  d_cache_is_clean = true;
  d_term_to_dreal_cache.clear();
  d_dreal_to_term_cache.clear();
  d_permanent_terms.clear();
}

dreal_term_cache::tm_to_cache_map::~tm_to_cache_map() {
  tm_to_cache_map::map_type::iterator it = s_tm_to_cache_map.map.begin();
  for (; it != s_tm_to_cache_map.map.end(); ++ it) {
    delete it->second;
  }
}

dreal_term_cache* dreal_term_cache::get_cache(expr::term_manager& tm) {
  dreal_term_cache* cache = 0;

  // Try to find an existing one
  tm_to_cache_map::map_type::const_iterator find = s_tm_to_cache_map.map.find(tm.id());
  if (find != s_tm_to_cache_map.map.end()) {
    cache = find->second;
  } else {
    cache = new dreal_term_cache(tm);
    s_tm_to_cache_map.map[tm.id()] = cache;
  }
  
  return cache;
}

void dreal_term_cache::gc() {
  if (!d_cache_is_clean) {

    // Create a new cache that contains just the variables
    d_term_to_dreal_cache.clear();
    d_dreal_to_term_cache.clear();

    // We're clean now
    d_cache_is_clean = true;
  }
}

void dreal_term_cache::gc_collect(const expr::gc_relocator& gc_reloc) {
  d_term_to_dreal_cache.reloc(gc_reloc);
  d_dreal_to_term_cache.reloc(gc_reloc);
  gc_reloc.reloc(d_permanent_terms);
}


}
}

#endif
