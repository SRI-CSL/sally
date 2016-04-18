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
#ifdef WITH_Z3

#include "smt/z3/z3_term_cache.h"
#include "expr/gc_relocator.h"

#include <iomanip>
#include <iostream>
#include <fstream>

#define unused_var(x) { (void)x; }

namespace sally {
namespace smt {

z3_term_cache::z3_term_cache(expr::term_manager& tm)
: gc_participant(tm, false)
, d_tm(tm)
, d_cache_is_clean(true)
{
  // Global configuration
  Z3_config cfg = Z3_mk_config();
  Z3_set_param_value(cfg, "MODEL", "true");

  // Make the context and set it to
  d_ctx = Z3_mk_context_rc(cfg);
  d_hasher.ctx = d_ctx;
  d_z3_to_term_cache = z3_to_term_cache(d_hasher);

  Z3_del_config(cfg);
}

z3_term_cache::~z3_term_cache() {
  clear();
  Z3_del_context(d_ctx);
}

z3_term_cache::tm_to_cache_map z3_term_cache::s_tm_to_cache_map;

void z3_term_cache::set_term_cache(expr::term_ref t, Z3_ast t_z3) {
  assert(d_term_to_z3_cache.find(t) == d_term_to_z3_cache.end());

  d_term_to_z3_cache[t] = t_z3;
  Z3_inc_ref(d_ctx, t_z3);

  // If a variable, remember it
  if (d_tm.term_of(t).op() == expr::VARIABLE) {
    d_permanent_terms.push_back(t);
    d_permanent_terms_z3.push_back(t_z3);
  } else {
    // Mark cache as dirty
    d_cache_is_clean = false;
  }

  // If enabled, check the term transformations by producing a series of
  // smt2 queries. To check run the contrib/smt2_to_z3.sh script and then
  // run on z3.
  if (output::trace_tag_is_enabled("z3::terms")) {
    static size_t k = 0;
    std::stringstream ss;
    ss << "z3_term_query_" << std::setfill('0') << std::setw(5) << k++ << ".smt2";
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
    Z3_string repr = Z3_ast_to_string(d_ctx, t_z3);
    query << "(assert (not (= " << repr << " " << t << ")))" << std::endl;

    query << "(check-sat)" << std::endl;
    d_tm.set_name_transformer(0);
  }
}

void z3_term_cache::set_term_cache(Z3_ast t_z3, expr::term_ref t) {
  assert(d_z3_to_term_cache.find(t_z3) == d_z3_to_term_cache.end());

  d_z3_to_term_cache[t_z3] = t;
  Z3_inc_ref(d_ctx, t_z3);

  // If a variable, remember it
  if (d_tm.term_of(t).op() == expr::VARIABLE) {
    d_permanent_terms.push_back(t);
    d_permanent_terms_z3.push_back(t_z3);
  } else {
    // Mark cache as dirty
    d_cache_is_clean = false;
  }

  // If enabled, check the term transformations by producing a series of
  // smt2 queries. To check run the contrib/smt2_to_z3.sh script and then
  // run on z3.
  if (output::trace_tag_is_enabled("z3::terms")) {
    static size_t k = 0;
    std::stringstream ss;
    ss << "z3_term_query_" << std::setfill('0') << std::setw(5) << k++ << ".smt2";
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
    Z3_string repr = Z3_ast_to_string(d_ctx, t_z3);
    query << "(assert (not (= " << repr << " " << t << ")))" << std::endl;

    query << "(check-sat)" << std::endl;
    d_tm.set_name_transformer(0);
  }
}

Z3_ast z3_term_cache::get_term_cache(expr::term_ref t) const {
  term_to_z3_cache::const_iterator find = d_term_to_z3_cache.find(t);
  if (find != d_term_to_z3_cache.end()) {
    return find->second;
  } else {
    return 0;
  }
}

expr::term_ref z3_term_cache::get_term_cache(Z3_ast t) const {
  z3_to_term_cache::const_iterator find = d_z3_to_term_cache.find(t);
  if (find != d_z3_to_term_cache.end()) {
    return find->second;
  } else {
    return expr::term_ref();
  }
}

void z3_term_cache::clear() {

  term_to_z3_cache::const_iterator it1 = d_term_to_z3_cache.begin();
  for (; it1 != d_term_to_z3_cache.end(); ++ it1) {
    Z3_dec_ref(d_ctx, it1->second);
  }

  z3_to_term_cache::const_iterator it2 = d_z3_to_term_cache.begin();
  for (; it2 != d_z3_to_term_cache.end(); ++ it2) {
    Z3_dec_ref(d_ctx, it2->first);
  }

  d_cache_is_clean = true;
  d_term_to_z3_cache.clear();
  d_z3_to_term_cache.clear();
  d_permanent_terms.clear();
  d_permanent_terms_z3.clear();

}

z3_term_cache::tm_to_cache_map::~tm_to_cache_map() {
  tm_to_cache_map::map_type::iterator it = s_tm_to_cache_map.map.begin();
  for (; it != s_tm_to_cache_map.map.end(); ++ it) {
    delete it->second;
  }
}

z3_term_cache* z3_term_cache::get_cache(expr::term_manager& tm) {

  z3_term_cache* cache = 0;

  // Try to find an existing one
  tm_to_cache_map::map_type::const_iterator find = s_tm_to_cache_map.map.find(tm.id());
  if (find != s_tm_to_cache_map.map.end()) {
    cache = find->second;
  } else {
    cache = new z3_term_cache(tm);
    s_tm_to_cache_map.map[tm.id()] = cache;
  }

  return cache;
}

void z3_term_cache::gc() {
  if (!d_cache_is_clean) {
    assert(false);
  }
}

void z3_term_cache::gc_collect(const expr::gc_relocator& gc_reloc) {
  d_term_to_z3_cache.reloc(gc_reloc);
  d_z3_to_term_cache.reloc(gc_reloc);
  gc_reloc.reloc(d_permanent_terms);
}

}
}

#endif
