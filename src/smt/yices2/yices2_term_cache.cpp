#ifdef WITH_YICES2

#include "smt/yices2/yices2_term_cache.h"

#include <iomanip>
#include <iostream>
#include <fstream>

namespace sally {
namespace smt {

yices2_term_cache::yices2_term_cache(expr::term_manager& tm)
: d_tm(tm)
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
  if (added) {
    d_cache_is_clean = false;
  }
  assert(added);

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
}

yices2_term_cache* yices2_term_cache::attach_to_cache(expr::term_manager& tm, const yices2_internal* instance) {

  yices2_term_cache* cache = 0;

  // Try to find an existing one
  tm_to_cache_map::const_iterator find = s_tm_to_cache_map.find(&tm);
  if (find != s_tm_to_cache_map.end()) {
    cache = find->second;
  } else {
    cache = new yices2_term_cache(tm);
  }
  cache->d_all_yices_instances.insert(instance);

  return cache;
}

void yices2_term_cache::detach_from_cache(const yices2_internal* instance) {
  d_all_yices_instances.erase(instance);
  if (d_all_yices_instances.size() == 0) {
    clear();
  }
}

void yices2_term_cache::gc() {
  if (!d_cache_is_clean) {
    // Get assertions from all yices2 instances
    std::set<expr::term_ref> all_terms;
    std::set<expr::term_ref> all_variables;
    std::set<const yices2_internal*>::const_iterator yices2_it = d_all_yices_instances.begin();

    // Get the root terms of all instances
    for (; yices2_it != d_all_yices_instances.end(); ++ yices2_it) {
      (*yices2_it)->get_assertions(all_terms);
      (*yices2_it)->get_variables(all_terms);
      (*yices2_it)->get_variables(all_variables);
    }

    // Get a list for yices2 terms to keep
    term_t* terms_to_keep = new term_t[all_terms.size()];
    std::set<expr::term_ref>::const_iterator it_y = all_terms.begin();
    for (size_t i = 0; it_y != all_terms.end(); ++ it_y, ++ i) {
      term_t to_keep = get_term_cache(*it_y);
      if (to_keep != NULL_TERM) {
        terms_to_keep[i] = to_keep;
      }
    }

    // Collect the garbage
    yices_garbage_collect(terms_to_keep, all_terms.size(), NULL, 0, true);
    delete terms_to_keep;

    // Create a new cache that contains just the variables
    term_to_yices_cache new_term_to_yices_cache;
    yices_to_term_cache new_yices_to_term_cache;
    std::set<expr::term_ref>::const_iterator vars_it = all_variables.begin();
    for (; vars_it != all_variables.end(); ++ vars_it) {
      expr::term_ref var = *vars_it;
      term_t var_yices = get_term_cache(var);
      if (var_yices != NULL_TERM) {
        new_term_to_yices_cache[var] = var_yices;
        new_yices_to_term_cache[var_yices] = var;
      }
    }

    // Swap in the new cache
    d_term_to_yices_cache.swap(new_term_to_yices_cache);
    d_yices_to_term_cache.swap(new_yices_to_term_cache);

    // We're clean now
    d_cache_is_clean = true;
  }
}

}
}

#endif
