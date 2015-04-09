/*
 * gc_relocator.cpp
 *
 *  Created on: Apr 9, 2015
 *      Author: dejan
 */

#include "expr/gc_relocator.h"

namespace sally {
namespace expr {

gc_info::gc_info(term_manager& tm, const relocation_map& gc_reloc)
: d_tm(tm)
, d_relocation_map(gc_reloc)
{}

void gc_info::collect(expr::term_ref& t) const {
  relocation_map::const_iterator find = d_relocation_map.find(t);
  if (find == d_relocation_map.end()) {
    t = find->second;
  } else {
    t = expr::term_ref();
  }
}

void gc_info::collect(expr::term_ref_strong& t) const {
  relocation_map::const_iterator find = d_relocation_map.find(t);
  if (find == d_relocation_map.end()) {
    t = expr::term_ref_strong(d_tm, find->second);
  } else {
    t = expr::term_ref_strong();
  }
}


}
}

