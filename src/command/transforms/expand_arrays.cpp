#include "expr/term_visitor.h"
#include "expand_arrays.h"
#include "term_utils.h"

#include <boost/unordered_map.hpp>
#include <boost/iterator/transform_iterator.hpp>
#include <boost/iterator/reverse_iterator.hpp>
#include <iostream>
#include <sstream>

namespace sally {
namespace cmd {
namespace transforms {

using namespace expr;

/** 
    Expand arrays by removing quantifiers, array lambda terms,
    and removing array variables involved in equality terms.
 **/
class expand_arrays_visitor {
public:
  
  typedef std::pair<integer, integer> interval_t;
  typedef boost::unordered_map<term_ref, interval_t, term_ref_hasher> var_to_interval_map;

  template<typename Map>
  struct take_second :
    std::unary_function<typename Map::value_type, typename Map::mapped_type> {
    typename Map::mapped_type operator()(typename Map::value_type p) const
    { return p.second; }
  };  

  typedef term_manager::substitution_map term_to_term_map;
  
  expand_arrays_visitor(term_manager& tm, term_to_term_map &subst_map);

  // Non-null terms are good
  bool is_good_term(term_ref t) const {
    return !t.is_null();
  }

  /** Get the children of the term t */
  void get_children(term_ref t, std::vector<term_ref>& children) {
    const term& t_term = d_tm.term_of(t);
    for (size_t i = 0; i < t_term.size(); ++ i) {
      children.push_back(t_term[i]);
    }
  }

  /** We visit only nodes that are not types, constants or variables */
  visitor_match_result match(term_ref t) {
    if (d_tm.is_type(t) || d_tm.term_of(t).op() == VARIABLE ||
	d_tm.term_of(t).op() == CONST_BOOL ||
	d_tm.term_of(t).op() == CONST_RATIONAL ||
	d_tm.term_of(t).op() == CONST_BITVECTOR ||
	d_tm.term_of(t).op() == CONST_ENUM ||
	d_tm.term_of(t).op() == CONST_STRING) {
      // Don't visit children or this node or the node
      return DONT_VISIT_AND_BREAK;
    }
    
    if (d_subst_map.find(t) == d_subst_map.end()) {
      // Visit the children if needed and then the node
      return VISIT_AND_CONTINUE;
    } else {
      // Don't visit children or this node or the node
      return DONT_VISIT_AND_BREAK;
    }
  }
  
  /** Visit the term and expand arrays (children already expanded) */
  void visit(term_ref t_ref);

private:

  
  term_manager& d_tm;
  term_to_term_map& d_subst_map; 

  void error(term_ref t_ref, std::string message) const;
  void get_array_type_bounds(term_ref t_ref, std::vector<interval_t> &bounds);
  
  void process_quantifier(term_ref t_ref, var_to_interval_map &imap);
  term_ref process_array_lambda(term_ref t_ref, var_to_interval_map &imap);
};

void expand_arrays_visitor::error(term_ref t_ref, std::string message) const {
  std::stringstream ss;
  term_manager* tm = output::get_term_manager(std::cerr);
  if (tm->get_internal() == d_tm.get_internal()) {
    output::set_term_manager(ss, tm);
  }
  ss << "Can't expand arrays " << t_ref;
  if (message.length() > 0) { ss << "(" << message << ")"; }
  ss << ".";
  throw exception(ss.str());
}

/* 
   (forall ( (i (subtype ((x Int)) (and (>= x 1) (<= x 4))))
             (j (subtype ((x Int)) (and (>= x 1) (<= x 4))))) Body)
   imap = { i -> (1,4), j -> (1,4) } 
*/
void expand_arrays_visitor::process_quantifier(term_ref ref, var_to_interval_map &imap) {
  assert (d_tm.op_of(ref) == TERM_EXISTS || d_tm.op_of(ref) == TERM_FORALL);

  std::vector<term_ref> quantified_vars;
  d_tm.get_quantifier_variables(ref, quantified_vars);
  for (unsigned i=0; i < quantified_vars.size(); ++i) {
    term_ref quantified_var = quantified_vars[i];
    // try to figure out if the quantified variable is bounded and if
    // yes then it extracts the lower and upper bounds
    if (imap.find(quantified_var) == imap.end()) {
      interval_t interval;
      if (d_tm.term_of(d_tm.type_of(quantified_var)).op() == TYPE_BOOL) {
	// XXX: array terms can only have sort Int -> Int|Real. If the
	// quantifier variable is of bool type and used as array index
	// the back-end solvers will complain.  A tempting solution is
	// to add an interval (0,1) from Bool. However, this won't
	// type check. TODO: The solution is to change the index types
	// of the arrays by replacing Bool with [0..1].
	error(ref, "quantifier variable cannot be of bool type");	
	imap.insert(std::make_pair(quantified_var, interval_t(integer((long) 0),integer(1))));
      } else if (expr::utils::get_bounds_from_pred_subtype(d_tm, d_tm.type_of(quantified_var), interval)) {
	imap.insert(std::make_pair(quantified_var, interval));
      } else {
	error(ref, "array is not statically bounded");	
      }
    }
  }
}

/*
     (array ((i (subtype ((x Int)) (and (>= x 1) (<= x 4))))) 
     (array ((j (subtype ((x Int)) (and (>= x 1) (<= x 4))))) 0)))
     imap = { i ->(1,4), j->(1,4) }
     return value = 0
 */
term_ref expand_arrays_visitor::process_array_lambda(term_ref ref, var_to_interval_map &imap) {
		     
  const term& t = d_tm.term_of(ref);
  term_op op = t.op();
  
  if (op == TERM_ARRAY_LAMBDA) {
    assert (t.size () == 2);
    term_ref index_t = t[0];
    term_ref body_t = t[1];
    expr::utils::interval_t itv;
    if (d_tm.term_of(d_tm.type_of(index_t)).op() == TYPE_BOOL) {
      error(ref, "array index cannot be bool");      
    } else if (expr::utils::get_bounds_from_pred_subtype(d_tm, d_tm.type_of(index_t), itv)) {    
      imap.insert(std::make_pair(index_t, itv));
      return process_array_lambda(body_t, imap); // recursive
    } else {
      error(ref, "array is not statically bounded");
    }
  }
  return ref;
}

void expand_arrays_visitor::get_array_type_bounds(term_ref ref, std::vector<interval_t> &bounds) {
  const term& t = d_tm.term_of(ref);
  term_op op = t.op();
  
  if (op == TYPE_ARRAY) {
    assert (t.size () == 2);
    term_ref index_type = t[0];
    term_ref element_type = t[1];
    expr::utils::interval_t itv;
    if (d_tm.term_of(index_type).op() == TYPE_BOOL) {
      error(ref, "array index cannot be bool");
    } else if (expr::utils::get_bounds_from_pred_subtype(d_tm, index_type, itv)) {     
      bounds.push_back(itv);
      get_array_type_bounds(element_type, bounds); // recursive
    } else {
      error(ref, "array is not statically bounded");
    }
  }
}
  
expand_arrays_visitor::expand_arrays_visitor(term_manager& tm, term_to_term_map &subst_map)
: d_tm(tm),
  d_subst_map(subst_map)
{}


/** 
    The visitor is building the new expanded term in d_subst_map.  The
    visitor traverses the term in a bottom-up fashion and when
    necessary uses the mapped term (QF terms) rather than the original
    term. For instance, this ensures that if at anytime the subterm at
    hand is a quantifier then its body cannot have quantifiers. This
    allows to remove safely all quantifiers even if the term is not in
    prenex normal form.
**/
void expand_arrays_visitor::visit(term_ref t_ref) {
  // pre: children have been already processed and the result is
  // already in d_subst_map.
  
  const term& t = d_tm.term_of(t_ref);
  term_op op = t.op();
  switch (op) {
  case TERM_EQ: {
    term_ref t0 = t[0];
    term_ref t1 = t[1];
    bool is_t0_array = d_tm.is_array_type(d_tm.type_of(t0));
    bool is_t1_array = d_tm.is_array_type(d_tm.type_of(t1));
    
    /** Equality between array lambda and array variable **/
    if (d_tm.term_of(t0).op() == TERM_ARRAY_LAMBDA || d_tm.term_of(t1).op() == TERM_ARRAY_LAMBDA) {
      /*
	(= |OM_state_type::state.cx| 
           (array ((i (subtype ((x Int)) (and (>= x 1) (<= x 4))))) 
   	       (array ((j (subtype ((x Int)) (and (>= x 1) (<= x 4))))) j))) 
        is replaced with
        (and (= select(select(|OM_state_type::state.cx|, 1), 1) 1)
             ...
             (= select(select(|OM_state_type::state.cx|, 1), 4) 4)
             ...	   
             (= select(select(|OM_state_type::state.cx|, 4), 4) 4))
      */

      term_ref a_lambda_t, var_t;
      if (d_tm.term_of(t0).op() ==  TERM_ARRAY_LAMBDA) {
	a_lambda_t = t0;
	var_t = t1;
      } else {
	a_lambda_t = t1;
	var_t = t0;
      }
      assert(d_tm.term_of(var_t).op() == VARIABLE);
      a_lambda_t = (!d_subst_map[a_lambda_t].is_null() ? d_subst_map[a_lambda_t]: a_lambda_t);
      
      std::vector<interval_t> array_type_bounds;
      var_to_interval_map imap;
      std::vector<std::vector<integer> > instantiations;
      std::vector<std::vector<integer> >::const_iterator it, et;	
      std::vector<term_ref> flatten_equalities;
      
      get_array_type_bounds(d_tm.type_of(var_t), array_type_bounds);
      // populate imap and return the innermost body term
      term_ref innermost_body = process_array_lambda(a_lambda_t, imap);
      // expanded_innermost_body is an expanded formula
      term_ref expanded_innermost_body = d_tm.substitute(innermost_body, d_subst_map);          
      //term_ref expanded_innermost_body = (!d_subst_map[innermost_body].is_null() ? d_subst_map[innermost_body]: innermost_body);
      
      if (imap.size() != array_type_bounds.size()) {
	error(t_ref, "unimplemented case: array accesses must be fully indexed");
      } else {
	expr::utils::create_all_instantiations(
		 boost::make_transform_iterator(imap.begin(), take_second<var_to_interval_map>()),	
		 boost::make_transform_iterator(imap.end(), take_second<var_to_interval_map>()),
		 instantiations);

	std::vector<std::vector<integer> >::const_iterator iit, iet;
	for (iit = instantiations.begin(), iet = instantiations.end(); iit!=iet; ++iit){
	  const std::vector<integer> &inst = *iit;
	  assert (!inst.empty());
	  
	  term_manager::substitution_map q_subst_map;	    
	  // replace indexes in the innermost_body
	  var_to_interval_map::const_iterator it, et;	    
	  unsigned i =0;
	  for (it = imap.begin(), et = imap.end(); it!=et; ++it, ++i) {
	    q_subst_map.insert(std::make_pair((*it).first,
			       d_tm.mk_rational_constant(rational(inst[i].get_signed(), 1))));
	  }
	  
	  // create unfolded read terms
	  term_ref read_ref = d_tm.mk_array_read(var_t, d_tm.mk_rational_constant((rational(inst[0].get_signed(), 1))));
	  for (unsigned idx=1; idx < inst.size(); ++idx) {
	    read_ref = d_tm.mk_array_read(read_ref , d_tm.mk_rational_constant(rational(inst[idx].get_signed(), 1)));
	  }
	  
	  flatten_equalities.push_back(d_tm.mk_term(TERM_EQ,
				       d_tm.substitute(expanded_innermost_body, q_subst_map), read_ref));
	}
	d_subst_map[t_ref] = d_tm.mk_and(flatten_equalities);
	return;
      }
    }
    /** Equality involving at least one array variable **/
    else if ((d_tm.term_of(t0).op() == VARIABLE && is_t0_array) ||
	(d_tm.term_of(t1).op() == VARIABLE && is_t1_array)) {      
      /*
        if (v (Array (subtype ((x Int)) (and (>= x 1) (<= x 4))) Real)) then 
	given (= |OM_state_type::next.v| |OM_state_type::state.v|) 
        is replaced with 
        (and (= select(|OM_state_type::next.v|, 1), select(|OM_state_type::state.v| 1))
             ...
             (= select(|OM_state_type::next.v|, 4), select(|OM_state_type::state.v| 4)))
      */
      std::vector<interval_t> bounds;
      std::vector<std::vector<integer> > instantiations;
      std::vector<std::vector<integer> >::iterator it, et;
      std::vector<term_ref> flatten_equalities;
          
      // note that all terms are well-typed so if both equality
      // operands are arrays they must have the same bounds.
      get_array_type_bounds(d_tm.type_of((is_t0_array ? t0 : t1)), bounds);
      expr::utils::create_all_instantiations(bounds.begin(), bounds.end(), instantiations);
      for (it = instantiations.begin(), et = instantiations.end(); it!=et; ++it){
	const std::vector<integer> &inst = *it;
	if (inst.empty()) continue; //this should not happen
	term_ref idx_term = d_tm.mk_rational_constant(rational(inst[0].get_signed(),1));
	term_ref unfolded_t0_ref = (is_t0_array ? d_tm.mk_array_read(t0 , idx_term) : t0);
	term_ref unfolded_t1_ref = (is_t1_array ? d_tm.mk_array_read(t1 , idx_term) : t1);
	for (unsigned idx=1; idx < inst.size(); ++idx) {
	  idx_term = d_tm.mk_rational_constant(rational(inst[idx].get_signed(), 1));
	  if (is_t0_array) {
	    // -- create t0[i1][i2]...[ik]
	    unfolded_t0_ref = d_tm.mk_array_read(unfolded_t0_ref , idx_term);
	  }
	  if (is_t1_array) {
	    // -- create t1[i1][i2]...[ik]	  
	    unfolded_t1_ref = d_tm.mk_array_read(unfolded_t1_ref , idx_term);
	  }
	}
	// -- create equality
	flatten_equalities.push_back(d_tm.mk_term(TERM_EQ, unfolded_t0_ref, unfolded_t1_ref));
      }
      d_subst_map[t_ref] = d_tm.mk_and(flatten_equalities);
      return;
    }
    break;
  }
  /** quantifiers (body might have array terms or not) **/
  case TERM_EXISTS:
  case TERM_FORALL: {
    /* 
       (forall ((i (subtype ((x Int)) (and (>= x 1) (<= x 4)))) 
                (j (subtype ((x Int)) (and (>= x 1) (<= x 4)))) e(i,j)))

        where e is some arbitrary term defined over quantified variables i and j,
	is replaced with 

        (and e(1,1) e(1,2)  ... e(1,4) e(2,1) ... e(4,4))
        where e(1,1) means the expression e where i and j have been substituted with 1.
    */
    var_to_interval_map imap;
    std::vector<std::vector<integer> > instantiations;
    
    process_quantifier(t_ref, imap);
    expr::utils::create_all_instantiations(
	   boost::make_transform_iterator(imap.begin(), take_second<var_to_interval_map>()),
	   boost::make_transform_iterator(imap.end(), take_second<var_to_interval_map>()),
	   instantiations);

    // body of the quantifier    
    term_ref body = d_tm.get_quantifier_body(t_ref);
    // qf_body is a quantifier-free formula
    term_ref qf_body = d_tm.substitute(body, d_subst_map);    
    //term_ref qf_body = (!d_subst_map[body].is_null() ? d_subst_map[body]: body);        

    std::vector<std::vector<integer> >::const_iterator iit, iet;
    std::vector<term_ref> qf_formulas;
    for (iit = instantiations.begin(), iet = instantiations.end(); iit!=iet; ++iit){
      const std::vector<integer> &inst = *iit;
      assert (!inst.empty());      
      
      term_manager::substitution_map q_subst_map;
      var_to_interval_map::const_iterator it, et;
      unsigned i=0;
      for (it = imap.begin(), et = imap.end(); it!=et; ++it, ++i) {
	rational v(inst[i].get_signed(), 1) ;
	q_subst_map.insert(std::make_pair((*it).first, d_tm.mk_rational_constant(v)));
      }
      qf_formulas.push_back(d_tm.substitute(qf_body, q_subst_map));
    }
    
    term_ref new_t_ref;    
    if (op == TERM_FORALL) {
      new_t_ref = d_tm.mk_and(qf_formulas);
    } else {
      new_t_ref = d_tm.mk_or(qf_formulas);      
    }
    d_subst_map[t_ref] = new_t_ref;
  }
  return;
  default: ;;    
  }

  
  // no transformation occurred!
  if (t.size() < 1) {
    d_subst_map[t_ref] = t_ref;
  } else {
    std::vector<term_ref> new_children;
    for(unsigned i=0; i < t.size(); ++i) {
      term_ref c = t[i];
      assert(!c.is_null());
      term_manager::substitution_map::iterator it = d_subst_map.find(c);
      if (it != d_subst_map.end()) {
	new_children.push_back(it->second);
      } else {
	new_children.push_back(c);
      }
    }

    // Need special cases for operators with payload    
    if (d_tm.term_of(t_ref).op() == TERM_BV_EXTRACT) {
      // Make a copy, in case we resize on construction
      bitvector_extract extract = d_tm.get_bitvector_extract(d_tm.term_of(t_ref));
      d_subst_map[t_ref] = d_tm.mk_bitvector_extract(new_children[0], extract);
    } else  if (d_tm.term_of(t_ref).op() == TERM_BV_SGN_EXTEND) {
      // Make a copy, in case we resize on construction
      bitvector_sgn_extend extend = d_tm.get_bitvector_sgn_extend(d_tm.term_of(t_ref));
      d_subst_map[t_ref] = d_tm.mk_bitvector_sgn_extend(new_children[0], extend); 
    } else {
      d_subst_map[t_ref] = d_tm.mk_term(op, new_children);
    }
  }
}

static term_ref rewrite(term_manager& tm, term_ref t)  {
  term_manager::substitution_map subst_map;
  typedef expand_arrays_visitor visitor_t;
  visitor_t visitor(tm, subst_map);
  term_visit_topological<visitor_t, term_ref, term_ref_hasher> visit_topological(visitor);
  visit_topological.run(t);
  return subst_map[t];        
}
  
expand_arrays::expand_arrays(system::context *ctx, std::string id)
: d_ctx(ctx), d_id(id) {}

  
static system::transition_system* apply_ts(system::context* ctx, std::string id,
					   const system::transition_system *ts) {

  term_manager &tm = ctx->tm();
  const system::state_type* st = ts->get_state_type();
  
  term_ref init = ts->get_initial_states();  
  term_ref tr = ts->get_transition_relation();

  system::state_formula* new_init =
    new system::state_formula(tm, st, rewrite(tm, init));

  system::transition_formula* new_tr =
    new system::transition_formula(tm, st, rewrite(tm, tr));

  system::transition_system* new_ts = new system::transition_system(st, new_init, new_tr);
  ctx->add_transition_system(id, new_ts);
  return new_ts;
}
  
static system::state_formula* apply_sf(system::context* ctx, std::string id,
				       const system::state_formula *sf) {
  term_manager &tm = ctx->tm();
  const system::state_type* st = sf->get_state_type();

  system::state_formula* new_sf =
    new system::state_formula(tm, st, rewrite(tm, sf->get_formula()));
  ctx->add_state_formula(id, new_sf);
  return new_sf;
}

void expand_arrays::apply(const system::transition_system *ts,
			  const std::vector<const system::state_formula*>& queries,
			  system::transition_system *& new_ts,
			  std::vector<const system::state_formula*>& new_queries) {
  
  new_ts = apply_ts(d_ctx, d_id, ts);
  new_queries.clear();
  new_queries.reserve(queries.size());
  for (std::vector<const system::state_formula*>::const_iterator it = queries.begin(),
	 et = queries.end(); it!=et; ++it) {
    new_queries.push_back(apply_sf(d_ctx, d_id, *it));
  }
  
}
  


}
}
}
