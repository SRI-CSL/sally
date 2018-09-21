//
// Created by Martin Blicha on 21.09.18.
//

#include "opensmt2_term_cache.h"

sally::smt::opensmt2_term_cache::opensmt2_term_cache()
{}

void sally::smt::opensmt2_term_cache::set_term_cache(sally::expr::term_ref t, PTRef ptref) {
  auto res = cache.insert(std::make_pair(t, ptref));
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
