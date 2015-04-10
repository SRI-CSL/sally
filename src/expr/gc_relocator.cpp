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

void gc_info::collect(std::vector<term_ref>& t_vec) const {
  for (size_t i = 0; i < t_vec.size(); ++ i) {
    collect(t_vec[i]);
  }
}

void gc_info::collect(std::vector<term_ref_strong>& t_vec) const {
  for (size_t i = 0; i < t_vec.size(); ++ i) {
    collect(t_vec[i]);
    assert(!t_vec[i].is_null());
  }
}

void gc_info::collect(std::deque<expr::term_ref>& t_deq) const {
  for (size_t i = 0; i < t_deq.size(); ++ i) {
    collect(t_deq[i]);
  }
}

void gc_info::collect(std::set<term_ref>& t_set) const {
  std::set<term_ref> new_t_set;
  std::set<term_ref>::const_iterator it = t_set.begin(), it_end = t_set.end();
  for (; it != it_end; ++ it) {
    term_ref t = *it;
    collect(t);
    if (!t.is_null()) {
      new_t_set.insert(t);
    }
  }
  new_t_set.swap(t_set);
}

void gc_info::collect(std::set<term_ref_strong>& t_set) const {
  std::set<term_ref_strong> new_t_set;
  std::set<term_ref_strong>::const_iterator it = t_set.begin(), it_end = t_set.end();
  for (; it != it_end; ++ it) {
    term_ref_strong t = *it;
    collect(t);
    assert(!t.is_null());
    new_t_set.insert(t);
  }
  new_t_set.swap(t_set);
}

void gc_info::collect(expr::term_manager::substitution_map& t_map) const {
  expr::term_manager::substitution_map new_map;
  expr::term_manager::substitution_map::const_iterator it = t_map.begin(), it_end = t_map.end();
  for (; it != it_end; ++ it) {
    expr::term_ref key = it->first;
    expr::term_ref value = it->second;
    collect(key);
    collect(value);
    if (!key.is_null() && !value.is_null()) {
      new_map[key] = value;
    }
  }
  new_map.swap(t_map);
}

void gc_info::collect(utils::symbol_table<expr::term_ref_strong>& t) const {

}

void gc_info::collect(utils::symbol_table<expr::term_ref>& t) const {

}


}
}

