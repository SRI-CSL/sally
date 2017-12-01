#include "expr/term_visitor.h"
#include "remove_quantifiers.h"
#include "term_utils.h"

#include <boost/unordered_map.hpp>
#include <iostream>
#include <sstream>

namespace sally {
namespace cmd {
namespace transforms {

class quantifier_subst_map_visitor {
public:
  
  typedef std::pair<expr::integer, expr::integer> interval_t;
  typedef boost::unordered_map<expr::term_ref, interval_t, expr::term_ref_hasher> var_to_interval_map;
  typedef expr::term_manager::substitution_map term_to_term_map;
  
  quantifier_subst_map_visitor(expr::term_manager& tm, term_to_term_map &subst_map);

  // Non-null terms are good
  bool is_good_term(expr::term_ref t) const {
    return !t.is_null();
  }

  /** Get the children of the term t that are relevant for the type computation */
  void get_children(expr::term_ref t, std::vector<expr::term_ref>& children);

  /** We visit only nodes that don't have types yet and are relevant for type computation */
  expr::visitor_match_result match(expr::term_ref t);

  /** Visit the term, compute type (children already type-checked) */
  void visit(expr::term_ref t_ref);

private:

  
  expr::term_manager& d_tm;
  term_to_term_map& d_subst_map; // quantifiers to non-quantifiers

  void error(expr::term_ref t_ref, std::string message) const;  
  bool get_quantified_vars(expr::term_ref t_ref, var_to_interval_map &imap);
  void create_all_instantiations(var_to_interval_map::const_iterator it,
				 var_to_interval_map::const_iterator et,
				 std::vector<std::vector<expr::integer> > &instantiations);
  
};

void quantifier_subst_map_visitor::error(expr::term_ref t_ref, std::string message) const {
  std::stringstream ss;
  expr::term_manager* tm = output::get_term_manager(std::cerr);
  if (tm->get_internal() == d_tm.get_internal()) {
    output::set_term_manager(ss, tm);
  }
  ss << "Can't remove quantifiers " << t_ref;
  if (message.length() > 0) { ss << "(" << message << ")"; }
  ss << ".";
  throw exception(ss.str());
}
  
/* 
   (forall ( (i (subtype ((x Int)) (and (>= x 1) (<= x 4))))
             (j (subtype ((x Int)) (and (>= x 1) (<= x 4))))) Body)
   qvmap = { i -> [1,4], j -> [1,4] } 
*/
bool quantifier_subst_map_visitor::get_quantified_vars(expr::term_ref quantifier,
						      var_to_interval_map &imap) {
  assert (d_tm.op_of(quantifier) == expr::TERM_EXISTS ||
	  d_tm.op_of(quantifier) == expr::TERM_FORALL);
  
  const expr::term& t = d_tm.term_of(quantifier);
  size_t n_args = t.size()-1;
  bool all_bounded = true;
  for (size_t i = 0; i < n_args; ++i) {
    expr::term_ref quantified_var = t[i];
    // try to figure out if the quantified variable is bounded and if
    // yes then it extracts the lower and upper bounds
    if (imap.find(quantified_var) == imap.end()) {
      interval_t interval;
      if (expr::utils::get_bounds_from_pred_subtype(d_tm, d_tm.type_of(quantified_var), interval)) {
	imap.insert(std::make_pair(quantified_var, interval));
      } else {
	all_bounded = false;
      }
    }
  }
  return all_bounded;
}

/** TODO: non-recursive **/
void quantifier_subst_map_visitor::
create_all_instantiations(var_to_interval_map::const_iterator it,
			  var_to_interval_map::const_iterator et,
			  std::vector<std::vector<expr::integer> > &instantiations) {
  if (it != et) {
    expr::integer lb = (*it).second.first;
    expr::integer ub = (*it).second.second;    
    var_to_interval_map::const_iterator next(it);
    create_all_instantiations(++next, et, instantiations);
    
    if (instantiations.empty()) {
      for (expr::integer i = lb ; i <= ub; ) {
	std::vector<expr::integer> singleton;
	singleton.push_back(i);
	instantiations.push_back(singleton);
	i = i + 1;
      }
    } else {
      std::vector<std::vector<expr::integer> > new_instantiations;      
      for (expr::integer i = lb ; i <= ub; ) {
	std::vector<std::vector<expr::integer> >::iterator  iit, iet;	
	for (iit = instantiations.begin(), iet = instantiations.end(); iit != iet; ++iit) {
	  std::vector<expr::integer> jj (*iit);
	  jj.insert(jj.begin(), i);
	  new_instantiations.push_back(jj);
	}
	i = i + 1;
      }
      std::swap(instantiations, new_instantiations);
    }
  }
}
  
quantifier_subst_map_visitor::quantifier_subst_map_visitor(expr::term_manager& tm, term_to_term_map &subst_map)
: d_tm(tm),
  d_subst_map(subst_map)
{}

void quantifier_subst_map_visitor::get_children(expr::term_ref t, std::vector<expr::term_ref>& children) {
  const expr::term& t_term = d_tm.term_of(t);
  for (size_t i = 0; i < t_term.size(); ++ i) {
    children.push_back(t_term[i]);
  }
}

expr::visitor_match_result quantifier_subst_map_visitor::match(expr::term_ref t) {
  if (d_subst_map.find(t) == d_subst_map.end()) {
    // Visit the children if needed and then the node
    return expr::VISIT_AND_CONTINUE;
  } else {
    // Don't visit children or this node or the node
    return expr::DONT_VISIT_AND_BREAK;
  }
}
  
void quantifier_subst_map_visitor::visit(expr::term_ref t_ref) {

  const expr::term& t = d_tm.term_of(t_ref);
  expr::term_op op = t.op();
  switch (op) {
  case expr::TERM_EXISTS:
  case expr::TERM_FORALL: {
    
    // -- extract all quantified variables and their bounds
    var_to_interval_map imap;
    if (!get_quantified_vars(t_ref, imap)) {
      error(t_ref, "");
    }
    
    std::vector<std::vector<expr::integer> > instantiations;
    create_all_instantiations(imap.begin(), imap.end(), instantiations);
    
    const expr::term& t = d_tm.term_of(t_ref);
    expr::term_ref body = t[t.size()-1];
    std::vector<std::vector<expr::integer> >::const_iterator iit, iet;
    std::vector<expr::term_ref> flatten_formulas;
    for (iit = instantiations.begin(), iet = instantiations.end(); iit!=iet; ++iit){
      const std::vector<expr::integer> &instantiation = *iit;
      expr::term_manager::substitution_map quantifier_subst_map;
      var_to_interval_map::const_iterator it, et;
      unsigned i=0;
      for (it = imap.begin(), et = imap.end(); it!=et; ++it, ++i) {
	expr::rational v(instantiation[i].get_signed(), 1) ;
	quantifier_subst_map.insert(std::make_pair((*it).first,
					d_tm.mk_rational_constant(v)));
      }
      expr::term_ref instantiated_body = d_tm.substitute(body, quantifier_subst_map);
      flatten_formulas.push_back(instantiated_body);
    }
    
    expr::term_ref new_t_ref;    
    if (op == expr::TERM_FORALL) {
      new_t_ref = d_tm.mk_and(flatten_formulas);
    } else {
      new_t_ref = d_tm.mk_or(flatten_formulas);      
    }

    d_subst_map[t_ref] = new_t_ref;
  }
    break;
  default: ;;
  }
}

remove_quantifiers::remove_quantifiers(system::context *ctx)
: d_ctx(ctx) {}
  
const system::transition_system *remove_quantifiers::apply(const system::transition_system *ts) {
  
  expr::term_ref init = ts->get_initial_states();  
  expr::term_ref tr = ts->get_transition_relation();

  // do not leak: client is responsible to free this pointer  
  system::state_formula * new_init =
    new system::state_formula(d_ctx->tm(), ts->get_state_type(),
			      expr::utils::rewrite<quantifier_subst_map_visitor>(init, d_ctx->tm()));
  
  system::transition_formula * new_tr =
    new system::transition_formula(d_ctx->tm(), ts->get_state_type(),
				   expr::utils::rewrite<quantifier_subst_map_visitor>(tr, d_ctx->tm()));
  
  const system::transition_system * new_ts =
    new system::transition_system(ts->get_state_type(), new_init, new_tr);
  
  return new_ts;
}
  
const system::state_formula *remove_quantifiers::apply(const system::state_formula *sf){
  
  // do not leak: client is responsible to free this pointer
  const system::state_formula * new_sf =
    new system::state_formula(d_ctx->tm(), sf->get_state_type(),
			      expr::utils::rewrite<quantifier_subst_map_visitor>(sf->get_formula(),
										 d_ctx->tm()));
  
  return new_sf;
}


}
}
}
