//
// Created by Martin Blicha on 21.09.18.
//

#ifdef WITH_OPENSMT2

#include "opensmt2_term_cache.h"

sally::smt::opensmt2_term_cache::opensmt2_term_cache()
{}

void sally::smt::opensmt2_term_cache::set_term_cache(sally::expr::term_ref t, PTRef ptref) {
  auto res = cache.insert(std::make_pair(t, ptref));
  (void) res;
  assert(res.second);
}

PTRef sally::smt::opensmt2_term_cache::get_term_cache(sally::expr::term_ref t) const {
  auto find = cache.find(t);
  if (find != cache.end()) {
    return find->second;
  } else {
    return PTRef_Undef;
  }
}

void sally::smt::opensmt2_term_cache::set_osmt_term_cache(PTRef ptref, sally::expr::term_ref t) {
  auto res = cache2.insert(std::make_pair(ptref, t));
  (void) res;
  assert(res.second);
}

sally::expr::term_ref sally::smt::opensmt2_term_cache::get_osmt_term_cache(PTRef ptref) const {
  auto find = cache2.find(ptref);
  if (find != cache2.end()) {
    return find->second;
  } else {
    return sally::expr::term_ref();
  }
}

#endif
