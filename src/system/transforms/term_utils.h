#pragma once

#include "expr/term.h"
#include "expr/term_manager.h"

namespace sally {
namespace expr {
namespace utils {

typedef std::pair<integer, integer> interval_t;

// return true if it succeeds
static inline bool term_to_integer(term_manager &tm, term_ref t_ref, integer &v) {
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
static inline bool get_lower_bound(term_manager &tm, term_ref t_ref, term_ref var, integer &lb) {
  term_op op = tm.op_of(t_ref);
  const term& t = tm.term_of(t_ref);
  if (op == TERM_GEQ) {
    if (t[0] == var) { // (>= v lb)
      return term_to_integer(tm, t[1], lb);
    }
  } else if (op == TERM_LEQ) {
    if (t[1] == var) { // (<= lb v)
      return term_to_integer(tm, t[0], lb);      
    }
  }
  return false;
}
 
// return true if it succeeds
static inline bool get_upper_bound(term_manager &tm, term_ref t_ref, term_ref var, integer &ub) {
  term_op op = tm.op_of(t_ref);
  const term& t = tm.term_of(t_ref);
  if (op == TERM_LEQ) {
    if (t[0] == var) { // (<= v ub)
      return term_to_integer(tm, t[1], ub);
    }
  } else if (op == TERM_GEQ) {
    if (t[1] == var) { // (>= ub v)
      return term_to_integer(tm, t[0], ub);
    }
  }
  return false;
}
 
// return true if suceeds
static inline bool get_bounds_from_pred_subtype(term_manager &tm, term_ref type_ref, interval_t &interval){
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

/** TODO: non-recursive **/
/* 
   Given a container [it,...et) of intervals [(1,4), (1, 3), (1,4)]
   produces [[1,1,1],..,[1,3,4],... [4,3,4]]
*/
template<typename IntervalIterator>  
static void create_all_instantiations(IntervalIterator it, IntervalIterator et, 
				      std::vector<std::vector<integer> > &instantiations) {
  if (it != et) {
    integer lb = (*it).first;
    integer ub = (*it).second;    
    IntervalIterator next(it);
    create_all_instantiations(++next, et, instantiations);
    
    if (instantiations.empty()) {
      for (integer i = lb ; i <= ub; ) {
	std::vector<integer> singleton;
	singleton.push_back(i);
	instantiations.push_back(singleton);
	i = i + 1;
      }
    } else {
      std::vector<std::vector<integer> > new_instantiations;      
      for (integer i = lb ; i <= ub; ) {
	std::vector<std::vector<integer> >::iterator  iit, iet;	
	for (iit = instantiations.begin(), iet = instantiations.end(); iit != iet; ++iit) {
	  std::vector<integer> jj (*iit);
	  jj.insert(jj.begin(), i);
	  new_instantiations.push_back(jj);
	}
	i = i + 1;
      }
      std::swap(instantiations, new_instantiations);
    }
  }
}
  

// The substitute method from term_manager replaces terms with
// terms. Here we replace terms that have a particular name with
// another term.
// FIXME: do this more efficiently.
  template<typename NameToTermMap>  
static inline term_ref name_substitute(term_manager &tm, term_ref t,
				       const NameToTermMap &subs_map) {
  
  if (std::distance(subs_map.begin(), subs_map.end()) == 0) {
    return t;
  } else {
    term_manager::substitution_map term_subs_map;    
    std::vector<term_ref> vars;
    tm.get_variables(t, vars);
    for (std::vector<term_ref>::const_iterator it = vars.begin(), et = vars.end(); it!=et; ++it){
      typename NameToTermMap::const_iterator t_it = subs_map.find(tm.get_variable_name(*it));
      if (t_it != subs_map.end()) {
	term_subs_map[*it] = t_it->second;
      }
    }
    return tm.substitute(t, term_subs_map);
  }
}
 
}
}
}

