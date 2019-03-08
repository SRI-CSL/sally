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

#include "chc_system.h"

#include "expr/term_manager.h"

#include <iostream>

using namespace sally::expr;

namespace sally {
namespace parser {

void chc_system::add_rule(term_ref head, term_ref tail) {

  // All the head variables should be distinct

  // Normalize head
  auto subst = normalize_head(head);
  // Normalize tail
  normalize_tail(tail, subst);

  d_rules[head].push_back(tail);
}

cmd::command* chc_system::to_commands() {
  if(is_transition_system()){
    return to_transition_system();
  }
  return 0;
}

bool chc_system::is_transition_system() const {
  size_t predicates = get_number_of_predicates();
  assert(predicates > 0);
  if (predicates > 1) { return false; }
  auto & tm = this->ctx.tm();
  bool single_init = false;
  bool single_update = false;
  bool single_query = false;
  for (auto it = d_rules.begin(); it != d_rules.end(); ++it) {
    const term_ref head = it->first;
    if (head == tm.mk_boolean_constant(false)) {
      // query
      single_query = it->second.size() == 1;
    }
    else { // the unique uninterpreted predicate
      auto predicate = get_predicate(head);
      auto& bodies = it->second;
      // There has to be exactly 2 rules: The init and the transition relation
      if (bodies.size() != 2) { return false;}
      for ( auto& body : bodies ) {
        term_vec subterms;
        tm.get_subterms(body, subterms);
        auto it = std::find_if(subterms.begin(), subterms.end(),
                               [=](term_ref sub) { return sub == predicate; });
        if (it == subterms.end()) {
          single_init = true;
        }
        else {
          single_update = true;
        }
      }
    }
  }
  return single_init && single_query && single_update;
}

size_t chc_system::get_number_of_predicates() const {
  // TODO: write properly; this is a quick workaround
  return d_rules.size() - 1;
}

substituition chc_system::normalize_head(term_ref &head) {
  substituition sub;
  auto& tm = ctx.tm();
  auto predicate = get_predicate(head);
  auto vars = get_arguments(head);

  auto it = d_normalized.find(predicate);
  if ( it == d_normalized.end()) {
    term_vec fresh_vars;
    for (int i = 0; i < vars.size(); ++i) {
      std::string fresh_name = tm.get_fresh_variable_name();
      term_ref type = tm.term_of(vars[i])[0];
      fresh_vars.push_back(tm.mk_variable(fresh_name, type));
    }
    auto res = d_normalized.insert(std::make_pair(predicate, fresh_vars));
    it = res.first;
  }

  // create substituition
  assert(vars.size() == it->second.size());
  for (int i = 0; i < vars.size(); ++i) {
    sub.add(vars[i], it->second[i]);
//    std::cout << vars[i] << ' ' << it->second[i] << std::endl;
  }
//  std::cout << "Before: " << head << '\n';
  head = ctx.tm().substitute(head, sub.mapping);
//  std::cout << "After: " << head << std::endl;
  return sub;
}

void chc_system::normalize_tail(term_ref &tail, const substituition &sub) {
  tail = ctx.tm().substitute(tail, sub.mapping);
}

expr::term_ref chc_system::get_predicate(expr::term_ref head) const {
  std::vector<term_ref> args;
  return *this->ctx.tm().term_of(head).begin();

}

chc_system::term_vec chc_system::get_arguments(expr::term_ref head) const {
  std::vector<term_ref> args;
  const term& term = this->ctx.tm().term_of(head);
  for(int i = 1; i < term.size(); ++i) {
    args.push_back(term.child(i));
  }
  return args;

}

cmd::command *chc_system::to_transition_system() const {
  return 0;
}

}
}


