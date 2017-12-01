#pragma once

#include "expr/term.h"
#include "expr/term_manager.h"

namespace sally {
namespace expr {
namespace utils {

typedef std::pair<integer, integer> interval_t;

// return true if it succeeds
static bool term_to_integer(term_ref t_ref, term_manager &tm, integer &v) {
  if (tm.op_of(t_ref) == CONST_RATIONAL) {
    const term& t = tm.term_of(t_ref);
    rational val = tm.get_rational_constant(t);
    if (val.is_integer()) {
      v = val.get_numerator();
      return true;
    }
  }
  return false;
}
  
  
// return true if it succeeds
static bool get_lower_bound(term_manager &tm, term_ref t_ref, term_ref var, integer &lb) {
  term_op op = tm.op_of(t_ref);
  const term& t = tm.term_of(t_ref);
  if (op == TERM_GEQ) {
    if (t[0] == var) { // (>= v lb)
      return term_to_integer(t[1], tm, lb);
    }
  } else if (op == TERM_LEQ) {
    if (t[1] == var) { // (<= lb v)
      return term_to_integer(t[0], tm, lb);      
    }
  }
  return false;
}
 
// return true if it succeeds
static bool get_upper_bound(term_manager &tm, term_ref t_ref, term_ref var, integer &ub) {
  term_op op = tm.op_of(t_ref);
  const term& t = tm.term_of(t_ref);
  if (op == TERM_LEQ) {
    if (t[0] == var) { // (<= v ub)
      return term_to_integer(t[1], tm, ub);
    }
  } else if (op == TERM_GEQ) {
    if (t[1] == var) { // (>= ub v)
      return term_to_integer(t[0], tm, ub);
    }
  }
  return false;
}
 
// return true if suceeds
static bool get_bounds_from_pred_subtype(term_manager &tm, term_ref type_ref, interval_t &interval){
  if (tm.op_of(type_ref) == TYPE_PREDICATE_SUBTYPE) {
    const term& ty = tm.term_of(type_ref);
    // XXX: if t_ref is well-typed ty[0] must be a variable
    term_ref body = ty[1];
    const term& tbody = tm.term_of(body);
    term_op opbody = tm.op_of(body);
    // XXX: search for (and p1 p2)
    if (opbody == TERM_AND && std::distance(tbody.begin(), tbody.end()) == 2) {
      integer lb, ub;
      if ( (get_lower_bound(tm, tbody[0], ty[0], lb) ||
	    get_lower_bound(tm, tbody[1], ty[0], lb)) &&
	   (get_upper_bound(tm, tbody[0], ty[0], ub) ||
	    get_upper_bound(tm, tbody[1], ty[0], ub))) {
	if (lb <= ub) /* well-formed interval*/ {
	  interval = interval_t(lb,ub);
	  return true;
	}
      }
    }
  }
  return false;
}

template<typename SubVisitor>
static expr::term_ref rewrite(expr::term_ref t, expr::term_manager& tm)  {
  expr::term_manager::substitution_map subst_map;    
  SubVisitor visitor(tm, subst_map);
  expr::term_visit_topological<SubVisitor, expr::term_ref, expr::term_ref_hasher> visit_topological(visitor);
  visit_topological.run(t);
  return tm.substitute(t, subst_map);        
}
 
}
}
}

