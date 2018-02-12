#include "expr/term_manager_internal.h"
#include "expr/term_manager.h"
#include "expr/term_visitor.h"

#include "remove_arrays.h"
#include "term_utils.h"

#include <boost/unordered_map.hpp>
#include <iostream>
#include <map>
#include <vector>

namespace sally {
namespace cmd {
namespace transforms {

using namespace expr;
  
typedef term_manager::substitution_map term_to_term_map;
typedef boost::unordered_map<std::string, term_ref> name_to_term_map;
  
typedef std::map<unsigned, term_ref> index_map_t;
typedef boost::unordered_map<std::string, index_map_t> arr_name_to_scalar_map;
typedef boost::unordered_map<term_ref, index_map_t, term_ref_hasher> arr_term_to_scalar_map;
typedef std::map<unsigned, std::pair<std::string, term_ref> > index_type_map_t;
typedef boost::unordered_map<std::string, index_type_map_t> arr_name_to_scalar_type_map;


class remove_arrays::remove_arrays_impl {

public:
  
  remove_arrays_impl(system::context *ctx, std::string id, const system::state_type *st);
  
  void apply (const system::transition_system* ts,
	      const std::vector<const system::state_formula*>& queries,
	      system::transition_system*& new_ts,
	      std::vector<const system::state_formula*>& new_queries);
  
private:
  
  system::context *d_ctx;
  std::string d_id;
  term_manager::substitution_map d_subs_map;
  /* map old array variable names with scalar terms */
  arr_name_to_scalar_map d_arr_name_map;
  /* map array terms to scalar terms */
  arr_term_to_scalar_map d_arr_term_map;  
  /* map old non-array variable names with new renamed terms */
  name_to_term_map d_non_arr_name_map;
  /* new state type after all arrays have been removed */
  system::state_type* d_new_st;
  
  void mk_state_type_without_arrays(const system::state_type *st);

  // extend d_new_st with (scalar) vars such that:
  // - vars are added as current vars
  // - state type is modified accordingly 
  void add_state_type_variables(const std::vector<term_ref>& vars,
				term_to_term_map& vars_map);
  
  term_ref mk_type_without_arrays(term_manager &tm, term_ref type_var, 
				  arr_name_to_scalar_type_map &arr_type_map,
				  std::set<std::string> &orig_scalar_vars);
  
  void mk_renaming_maps(term_manager &tm, term_ref type_var, term_ref vars_struct,
			const system::state_type* st, system::state_type::var_class vc,
			const arr_name_to_scalar_type_map &arr_type_map,
			const std::set<std::string> &non_arr_vars);
  
  term_ref apply_term(term_ref t);
};
  
remove_arrays::remove_arrays(const system::transition_system* original, system::context *ctx, std::string id, const system::state_type *st)
  : transform(original), m_pImpl(new remove_arrays_impl(ctx, id, st)) {}
  

remove_arrays::~remove_arrays() {
  delete m_pImpl;
}

void remove_arrays::apply (const system::transition_system* ts,
			   const std::vector<const system::state_formula*>& queries,
			   system::transition_system*& new_ts,
			   std::vector<const system::state_formula*>& new_queries) {
  m_pImpl->apply(ts, queries, new_ts, new_queries);
}
  

static void error(term_manager &tm, term_ref t_ref, std::string message) {
  std::stringstream ss;
  term_manager* _tm = output::get_term_manager(std::cerr);
  if (_tm->get_internal() == tm.get_internal()) {
    output::set_term_manager(ss, _tm);
  }
  ss << "Can't remove arrays " << t_ref;
  if (message.length() > 0) { ss << ". " << message; }
  ss << ".";
  throw exception(ss.str());
}

/**************************************************************************/  
/****                     Normalize terms                             *****/
/**************************************************************************/

// Certain array terms t cannot be removed without having an explicit
// name for them. After normalization, t is only allowed to appear in
// equalties of the form v = t where v is a fresh variable.
class term_normalizer {
public:
  
  typedef term_manager::substitution_map term_to_term_map;
  
  term_normalizer(term_manager& tm): d_tm(tm) { }

  term_ref normalize(term_ref t) {
    term_ref res = normalize_rec(t);
    for(term_to_term_map::iterator it = d_pending_equalities.begin(),
    	  et = d_pending_equalities.end(); it!=et; ++it) {
      res = d_tm.mk_term(TERM_AND, res,
			 d_tm.mk_term(TERM_EQ, it->first, d_subst[it->second]));
    }
    return res;
  }
  
private:
  term_manager& d_tm;
  term_to_term_map d_subst;
  term_to_term_map d_pending_equalities;
  
  term_ref normalize_rec(term_ref t) {
    
    term_to_term_map::const_iterator it = d_subst.find(t);
    if (it != d_subst.end()) {
      return it->second;
    }
    
    bool child_changed = false;
    std::vector<term_ref> children;
    for (size_t i = 0; i < d_tm.term_of(t).size(); ++ i) {
      term_ref child = d_tm.term_of(t)[i];
      term_ref child_subst = normalize_rec(child); // recursive call
      if (child_subst != child) {
	child_changed = true;
      }
      children.push_back(child_subst);
    }
    // all children have been normalized already
    
    term_op op = d_tm.term_of(t).op();
    if (!child_changed &&
	(op != TERM_ITE &&
	 op != TERM_AND && op != TERM_OR && op != TERM_XOR &&
	 op != TERM_ARRAY_READ && op != TERM_ARRAY_WRITE)) {
      d_subst[t] = t;
      return t;
    }
    
    term_ref t_new;
    // Need special cases for operators with payload
    switch (op) {
    case TERM_BV_EXTRACT: {
      // Make a copy, in case we resize on construction
      bitvector_extract extract = d_tm.get_bitvector_extract(d_tm.term_of(t));
      t_new = d_tm.mk_bitvector_extract(children[0], extract);
      break;
    }
    case TERM_BV_SGN_EXTEND: {
      // Make a copy, in case we resize on construction
      bitvector_sgn_extend extend = d_tm.get_bitvector_sgn_extend(d_tm.term_of(t));
      t_new = d_tm.mk_bitvector_sgn_extend(children[0], extend); 
      break;
    }
    case TERM_TUPLE_READ:
    case TERM_TUPLE_WRITE: {
      break;
    }
    /* BEGIN NORMALIZED TERMS **/
    //case TERM_ITE:        
    //case TERM_ARRAY_READ:
    // if (!d_tm.is_array_type(d_tm.type_of(t))) {
    //   t_new = d_tm.mk_term(op,children);
    //   break;
    // } else {
    //   // normalize
    // }
    case TERM_ARRAY_WRITE: {
      // replace term with an auxiliary variable and remember the map
      // in the queue.
      t_new = d_tm.mk_term(op, children);
      term_ref t_type = d_tm.type_of(t);     
      term_ref var = d_tm.mk_variable(d_tm.get_fresh_variable_name(), t_type);
      term_ref placeholder = d_tm.mk_variable(d_tm.get_fresh_variable_name(), t_type);
      d_subst[placeholder] = t_new;
      d_pending_equalities.insert(std::make_pair(var, placeholder));
      //d_queue.push_back(std::make_pair(var, placeholder));
      d_subst[t] = var;
      return var;
    }
    /* END NORMALIZED TERMS **/    
    // case TERM_AND:
    // case TERM_OR:
    // case TERM_XOR: {
      // Given (f1 op ... op fn) we create a new term (&& x_i = y_i)
      // && (f1 op ... op fn) where (x_i,y_i) \in queue.
      // In other words, the equalities are conjoined with the nearest
      // top-level boolean operator.
      // if (!d_queue.empty()) {
      // 	t_new = d_tm.mk_term(op, children);      
      // 	while(!d_queue.empty()) {
      // 	  std::pair<term_ref, term_ref> p = d_queue.back();
      // 	  t_new = d_tm.mk_term(TERM_AND, t_new, d_tm.mk_term(TERM_EQ, p.first,
      // 							     d_subst[p.second]));
      // 	  d_queue.pop_back();		
      // 	}
      // 	d_subst[t] = t_new;
      // 	return t_new;
      // } else {
      // 	// go to default
      // }
      //}
    default:
      t_new = d_tm.mk_term(op, children);
    }
    
    d_subst[t] = t_new;
    return t_new;
  }
  
};

/**************************************************************************/  
/*                    Remove array write terms                            */
/*                                                                        */
/* Preconditions: all arrays have been expanded.                          */  
/**************************************************************************/
class remove_write_terms {
private:

  // read-over-write transformation:
  //    read(write(A,i,v),j) = if i==j then v else read(A,j)
  class read_over_write_visitor {
  public:
  
    read_over_write_visitor(term_manager& tm, term_to_term_map& subst_map)
      : d_tm(tm), d_subst_map(subst_map) {}
    

    // Non-null terms are good
    bool is_good_term(term_ref t) const {
      return !t.is_null();
    }

    void get_children(term_ref t_ref, std::vector<term_ref>& children) {
      const term& t = d_tm.term_of(t_ref);
      for (size_t i = 0; i < t.size(); ++ i) {
	children.push_back(t[i]);
      }
    }
    
    visitor_match_result match(term_ref t) {
      if (d_tm.term_of(t).op() == TERM_ARRAY_LAMBDA ||
	  d_tm.term_of(t).op() == TERM_FORALL ||
	  d_tm.term_of(t).op() == TERM_EXISTS) {
	error(d_tm, t, "This term cannot be processed by read_over_write_visitor");
      }
      if (d_subst_map.find(t) != d_subst_map.end()) {
	// Don't visit children or this node or the node
	return DONT_VISIT_AND_BREAK;
      } else if (d_tm.term_of(t).op() == TERM_ARRAY_READ) {
	// We stop at the top-level array read found
	return VISIT_AND_BREAK;
      } else {
	// Don't visit this node but visit children
	return DONT_VISIT_AND_CONTINUE;    
      }
  }
    
    /** Visit the term (children have not been processed) */
    void visit(term_ref t_ref) {
      assert (d_tm.term_of(t_ref).op() == TERM_ARRAY_READ);
      
      read_over_write(d_tm.get_array_read_array(t_ref), t_ref);
    }
    
  private:
    
    term_manager& d_tm;
    term_to_term_map& d_subst_map;

    // read(write(a, i , v), j) ---> ite(i=j, v, read(a,j))
    // 
    // examples: read(write(write(A, read(B,i), 7), x, 8, ), y) ~~>
    //           ite(x=y, 8, read(write(A,read(B,i), 7), y))    ~~>
    //           ite(x=y, 8, ite(read(B,i) == y, 7, read(A, y)))
    //                             
    //           read(write(A,read(B,i),v), x) ~>
    //           ite(read(B,i) == x, v, read(A, x))
    //
    // TODO: non-recursive
    term_ref read_over_write(term_ref child, term_ref parent){
      
      term_to_term_map::iterator it = d_subst_map.find(parent);
      if (it != d_subst_map.end())
	return it->second;
      
      assert(d_tm.term_of(parent).op() == TERM_ARRAY_READ);
      if (d_tm.term_of(child).op () == TERM_ARRAY_WRITE) {
	term_ref a = d_tm.get_array_write_array(child);
	term_ref i = d_tm.get_array_write_index(child);
	term_ref v = d_tm.get_array_write_element(child);
	term_ref j = d_tm.get_array_read_index(parent);
	term_ref t = read_over_write(a, d_tm.mk_array_read(a, j)); // recursive
	term_ref res = d_tm.mk_term(TERM_ITE, d_tm.mk_term(TERM_EQ, i, j), v, t);
	d_subst_map[parent] = res;
	return res;
      } else if (d_tm.term_of(child).op() == TERM_ARRAY_READ) {
	term_ref res = read_over_write(d_tm.get_array_read_array(child), child); // recursive
	d_subst_map[child] = res;
	return res;
      } else {
	return parent;
      }
    }
  };  

  // partial equalities transformation: 
  // 
  // b = write(a, i, v) 
  //             --> forall j \in [lb,ub]:: ite(i=j, b[j] = v, b[j] = a[j])
  //             --> (ite(i=lb  , select(b, lb) = v, select(b, lb) = select(a, lb)) and
  //                  ite(i=lb+1, select(b, lb+1) = v, select(b,lb+1) = select(a, lb+1)) and
  //                  ...
  //                  ite(i=ub  , select(b, ub) = v, select(b, ub) = select(a, ub)))
  class remove_partial_equalities_visitor {
  public:
  
    remove_partial_equalities_visitor(term_manager& tm, term_to_term_map& subst_map)
      : d_tm(tm), d_subst_map(subst_map) {}
    
    
    bool is_good_term(term_ref t) const {
      return !t.is_null();
    }
    
    void get_children(term_ref t_ref, std::vector<term_ref>& children) {
      const term& t = d_tm.term_of(t_ref);
      for (size_t i = 0; i < t.size(); ++ i) {
	children.push_back(t[i]);
      }
    }
    
    visitor_match_result match(term_ref t) {
      if (d_subst_map.find(t) != d_subst_map.end()) {
	// Don't visit children or this node or the node
	return DONT_VISIT_AND_BREAK;
      } else {
	return VISIT_AND_CONTINUE;
      }
    }

    // Pre: t_ref has been normalized so array write terms only appear
    // in equalities.
    void visit(term_ref t_ref) {
      if (d_tm.op_of(t_ref) == TERM_EQ) {
	term_ref t0,t1;	
	term_ref lhs_t, array_write_t;

	t0 = d_tm.term_of(t_ref)[0];
	t1 = d_tm.term_of(t_ref)[1];
	
	if (d_tm.term_of(t0).op() ==  TERM_ARRAY_WRITE) {
	  array_write_t = t0;
	  lhs_t = t1;
	} else if (d_tm.term_of(t1).op() ==  TERM_ARRAY_WRITE){
	  array_write_t = t1;
	  lhs_t = t0;
	} else {
	  return;
	}
	
	// ensured by normalization
	assert(d_tm.term_of(lhs_t).op() == VARIABLE);
	
	term_ref array_t = d_tm.get_array_write_array(array_write_t);
	term_ref i_t = d_tm.get_array_write_index(array_write_t);
	term_ref v_t = d_tm.get_array_write_element(array_write_t);        
	
	term_ref array_idx_ty = d_tm.get_array_type_index(d_tm.type_of(array_t));    
	expr::utils::interval_t itv;    
	if (expr::utils::get_bounds_from_pred_subtype(d_tm, array_idx_ty, itv)) {
	  unsigned long lb = itv.first.get_unsigned();
	  unsigned long ub = itv.second.get_unsigned();
	  std::vector<term_ref> new_t;      
	  for (unsigned j=lb; j<=ub; ++j) {
	    term_ref j_t = d_tm.mk_rational_constant(rational(j, 1));      	
	    new_t.push_back(d_tm.mk_term(TERM_ITE,
					 d_tm.mk_term(TERM_EQ, i_t, j_t),
					 d_tm.mk_term(TERM_EQ,
						      d_tm.mk_array_read(lhs_t, j_t),
						      v_t),
					 d_tm.mk_term(TERM_EQ,
						      d_tm.mk_array_read(lhs_t, j_t),
						      d_tm.mk_array_read(array_t, j_t))));
	  }
	  
	  d_subst_map[t_ref] = d_tm.mk_and(new_t);
	} else {
	  error(d_tm, t_ref, "array is not statically bounded");
	}
      }
    }
    
  private:
    term_manager& d_tm;
    term_to_term_map& d_subst_map; 
  };  

  
public:
  
  remove_write_terms(term_manager& tm): d_tm(tm) {}

  term_ref apply(term_ref t) {
    term_ref t_new;
    
    { // 1) apply read-over-write transformation
      // use brackets to avoid confusion between variables
      term_to_term_map subst_map;
      read_over_write_visitor visitor(d_tm, subst_map);
      term_visit_topological<read_over_write_visitor, term_ref, term_ref_hasher> tvt(visitor);
      tvt.run(t);
      t_new = d_tm.substitute(t, subst_map);
    }

    // 2) Normalize t_new so that array write terms can only appear in
    // equalities.
    // FIXME: we would like to skip this normalization because it adds
    //        auxiliary variables.  Currently,
    //        remove_partial_equalities_visitor and
    //        remove_read_visitor rely on it.
    term_normalizer tn(d_tm);
    t_new = tn.normalize(t_new);

    { // 3) remove the rest of array write terms
      term_to_term_map subst_map;
      remove_partial_equalities_visitor visitor(d_tm, subst_map);
      term_visit_topological<remove_partial_equalities_visitor, term_ref, term_ref_hasher> tvt(visitor);
      tvt.run(t_new);
      t_new = d_tm.substitute(t_new, subst_map);
    }
    return t_new;
  }

private:
  term_manager& d_tm;
};


// read((ite t1 (read (ite t2 a1 a2) i1) (read (ite t3 a3 a4) i2)), j) ~~~>
// ite t1 (ite t2 (read (read a1 i1) j) (read (read a2 i1) j))
//        (ite t3 (read (read a3 i2) j) (read (read a4 i2) j))
class read_over_ite {
public:
  
  typedef term_manager::substitution_map term_to_term_map;
  
  read_over_ite(term_manager& tm): d_tm(tm) { }
    
  term_ref apply(term_ref t) {

    term_to_term_map::const_iterator it = d_subst.find(t);
    if (it != d_subst.end()) {
      return it->second;
    }
    
    bool child_changed = false;
    std::vector<term_ref> children;
    for (size_t i = 0; i < d_tm.term_of(t).size(); ++ i) {
      term_ref child = d_tm.term_of(t)[i];
      term_ref child_subst = apply(child); // recursive call
      if (child_subst != child) {
	child_changed = true;
    }
      children.push_back(child_subst);
    }
    // all children have been transformed
    
    term_op op = d_tm.term_of(t).op();
    if (!child_changed &&
	(op != TERM_ITE &&
	 op != TERM_AND && op != TERM_OR && op != TERM_XOR &&
	 op != TERM_ARRAY_READ && op != TERM_ARRAY_WRITE)) {
      d_subst[t] = t;
      return t;
    }

    term_ref t_new;
    // Need special cases for operators with payload
    switch (op) {
    case TERM_BV_EXTRACT: {
      // Make a copy, in case we resize on construction
      bitvector_extract extract = d_tm.get_bitvector_extract(d_tm.term_of(t));
      t_new = d_tm.mk_bitvector_extract(children[0], extract);
      break;
    }
    case TERM_BV_SGN_EXTEND: {
      // Make a copy, in case we resize on construction
      bitvector_sgn_extend extend = d_tm.get_bitvector_sgn_extend(d_tm.term_of(t));
      t_new = d_tm.mk_bitvector_sgn_extend(children[0], extend); 
      break;
    }
    case TERM_TUPLE_READ:
    case TERM_TUPLE_WRITE: {
      break;
    }
    /* select(ite(t1,t2,t3), i) */  
    case TERM_ARRAY_READ: {
      if (d_tm.op_of(children[0]) == TERM_ITE) {
	t_new = push_down_read(children[0], children[1]);
	break;
      }
    }
    default:
      t_new = d_tm.mk_term(op, children);
    }
    
    d_subst[t] = t_new;
    return t_new;
  }
  
private:
  term_manager& d_tm;
  term_to_term_map d_subst;

  term_ref push_down_read(term_ref ref, term_ref idx) {
    assert(d_tm.is_array_type(d_tm.type_of(ref)));
    
    if (d_tm.op_of(ref) == TERM_ITE) {
      const term&t = d_tm.term_of(ref);      
      term_ref t1  = push_down_read(t[1], idx); //recursive call
      term_ref t2  = push_down_read(t[2], idx); //recursive call
      return d_tm.mk_term(t.op(), t[0], t1, t2);
    } else if (d_tm.op_of(ref) == VARIABLE ||
	       d_tm.op_of(ref) == TERM_ARRAY_READ) {
      return d_tm.mk_array_read(ref, idx); 
    } else {
      error(d_tm, ref, "Unsupported case in push_down_read");
      return ref;
    }
  }
};

  
/**************************************************************************/  
/*                 Remove array read terms                                */
/*                                                                        */
/* Preconditions: all arrays have been expanded and no array write terms. */
/**************************************************************************/    
class remove_read_visitor {
public:
  
  remove_read_visitor(term_manager& tm, term_to_term_map& subst_map,
		      const arr_name_to_scalar_map& arr_name_map,
		      arr_term_to_scalar_map& d_arr_term_map);

  bool is_good_term(term_ref t) const {
    return !t.is_null();
  }

  ////////////////////////////////////////////////////////////////////////
  // Given a term read(X,Y) we only visit its index (Y) but not X.
  // 
  // Note that X cannot contain array writes. Therefore, X can only
  // contain either an array variable or nested read terms. The latter
  // is covered by process_array_read.
  ////////////////////////////////////////////////////////////////////////
  void get_children(term_ref t, std::vector<term_ref>& children) {
    const term& t_term = d_tm.term_of(t);

    if (t_term.op() == TERM_ARRAY_READ) {
      // If the term is an array read we only visit its index or
      // indexes if t is a nested term of array reads.  The indexes
      // must be visited because they can contain another array read
      // term.
      term_ref c = t;
      while (d_tm.op_of(c) == TERM_ARRAY_READ) {
	children.push_back(d_tm.get_array_read_index(c));
	c = d_tm.get_array_read_array(c);
      }
    } else {
      for (size_t i = 0; i < t_term.size(); ++ i) {
	children.push_back(t_term[i]);
      }
    }
  }

  visitor_match_result match(term_ref t) {
    if (d_tm.term_of(t).op() == TERM_ARRAY_WRITE ||
	d_tm.term_of(t).op() == TERM_ARRAY_LAMBDA ||	
	d_tm.term_of(t).op() == TERM_FORALL ||
	d_tm.term_of(t).op() == TERM_EXISTS) {
      error(d_tm, t, "This term cannot be processed by remove_read_visitor");
    }
    if (d_subst_map.find(t) != d_subst_map.end()) {
      // Don't visit children or this node or the node
      return DONT_VISIT_AND_BREAK;
    } else if (d_tm.term_of(t).op() == TERM_ARRAY_READ) {
      // Visit array read children
      return VISIT_AND_CONTINUE; 
    } else {
      // Don't visit this node but visit children
      return DONT_VISIT_AND_CONTINUE;    
    }
  }

  /** Visit the term (children already processed) */
  void visit(term_ref t_ref);
  
private:
  
  term_manager& d_tm;
  term_to_term_map& d_subst_map; 
  const arr_name_to_scalar_map& d_arr_name_map;
  arr_term_to_scalar_map& d_arr_term_map;

  // ref is read(read(....,_),_)
  // return the array variable of the innermost read term and all the
  // index terms (indexes) together with the minimum/maximum value each index
  // can take (min_indexes/max_indexes).
  // 
  // Pre: ref is fully indexed (i.e., !is_array_type(type_of(ref)))
  term_ref process_read_array(term_ref ref,
			      std::vector<term_ref> &indexes,
			      std::vector<unsigned long> &min_indexes,
			      std::vector<unsigned long> &max_indexes);

  /*
    pre: 0 <= i < indices.size();
    pre: indices.size() == max_indices.size();

    Given indexes: i, 2, and, j with dimensions 3, 3, and 3 it produces:
    [[1,2,1],[1,2,2],[1,2,3],[2,2,1],[2,2,2],[2,2,3], [3,2,1],[3,2,2], [3,2,3]]
    Given indexes: 1, 2, and j with dimensions 3, 3, and 3 it produces:
    [[1,2,1],[1,2,2],[1,2,3]]
    Given indexes: 1, j, and 2 with dimensions 3, 3, and 3 it produces:
    [[1,1,2],[1,2,2],[1,3,2]]
   */
  void create_all_indexes_values(unsigned i,
				 const std::vector<term_ref> &indices,
				 const std::vector<unsigned long> &min_indices,
				 const std::vector<unsigned long> &max_indices,
				 std::vector<std::vector<unsigned long> > &indexes_values);

  /* map an array access to t denoted by indexes to a scalar variable */
  term_ref get_scalar_term(term_ref t, 
			   const std::vector<unsigned long> &indexes,
			   const std::vector<unsigned long> &min_indexes,
			   const std::vector<unsigned long> &max_indexes);
};
      
/* Return a number N from a sequence of indexes where
  N = ((range[0] * ... * range[k-2]) * (indices[0] - 1)) + 
      ((range[1] * ... * range[k-2]) * (indices[1] - 1)) + 
      ((range[2] * ... * range[k-2]) * (indices[2] - 1)) + 
      ...
      (range[k-2]                   * (indices[k-2]-1)) + 
      indices[k-1]

   where range[i] = max_indices[i] - min_indices[i] + 1
*/
static unsigned get_unidimensional_index(const std::vector<unsigned long> &indices,
					 const std::vector<unsigned long> &min_indices,
					 const std::vector<unsigned long> &max_indices) {
  assert (indices.size() > 0);
  assert (min_indices.size() == max_indices.size());
  assert (indices.size() == max_indices.size());
  
  unsigned r = 0;
  unsigned k = indices.size();  
  for (unsigned i=0; i < k; ++i) {
    unsigned v = 1;
    for (unsigned j=i; j < k-1; ++j) {
      v *= max_indices[j] - min_indices[j] + 1;
    }
      r += (v * ((i==k-1 ? indices[i] : indices[i] -1)));
  }
  return r;
}
      
term_ref remove_read_visitor::process_read_array(term_ref ref,
						 std::vector<term_ref>& indexes,
						 std::vector<unsigned long>& min_indexes,
						 std::vector<unsigned long>& max_indexes) {
  if (d_tm.op_of(ref) == TERM_ARRAY_READ) {
    term_ref a = d_tm.get_array_read_array(ref);
    term_ref i = d_tm.get_array_read_index(ref);
    term_ref i_ty = d_tm.get_array_type_index(d_tm.type_of(a));
    expr::utils::interval_t itv;    
    if (expr::utils::get_bounds_from_pred_subtype(d_tm, i_ty, itv)) {
      unsigned long lb = itv.first.get_unsigned();
      unsigned long ub = itv.second.get_unsigned();
      term_ref res = process_read_array(a, indexes, min_indexes, max_indexes);  // recursive
      // XXX: important to return the transformed version of the index
      indexes.push_back(d_tm.substitute(i, d_subst_map));
      min_indexes.push_back(lb);
      max_indexes.push_back(ub);
      return res;
    } else {
      error(d_tm, ref, "array is not statically bounded");
    }
  }
  
  return ref;
}
    
/** TODO: non-recursive **/
void remove_read_visitor::create_all_indexes_values(unsigned i,
						    const std::vector<term_ref> &indices,
						    const std::vector<unsigned long> &min_indices,
						    const std::vector<unsigned long> &max_indices,
						    std::vector<std::vector<unsigned long> > &indexes_values) {
  if (i < indices.size()) {
    unsigned long min_index = min_indices[i];    
    unsigned long max_index = max_indices[i];
    integer ind; 
    bool is_constant_index = expr::utils::term_to_integer(d_tm, indices[i], ind);
    unsigned long constant_index = 0;
    if (is_constant_index) {
      constant_index = ind.get_unsigned();
      // any value as long as they are equal
      min_index = 1;
      max_index = 1;
    }
    create_all_indexes_values(++i, indices, min_indices, max_indices, indexes_values); // recursive
    
    if (indexes_values.empty()) {
      for (unsigned long j=min_index; j <= max_index; ) {
	std::vector<unsigned long> singleton;
	singleton.push_back((is_constant_index ? constant_index : j));
	indexes_values.push_back(singleton);
	j = j + 1;
      }
    } else {
      std::vector<std::vector<unsigned long> > new_indexes_values;      
      for (unsigned long j=min_index ; j <= max_index; ) {
	std::vector<std::vector<unsigned long> >::iterator  it, et;	
	for (it = indexes_values.begin(), et = indexes_values.end(); it != et; ++it) {
	  std::vector<unsigned long> jj (*it);
	  jj.insert(jj.begin(), (is_constant_index ? constant_index: j));
	  new_indexes_values.push_back(jj);
	}
	j = j + 1;
      }
      std::swap(indexes_values, new_indexes_values);
    }
  }
}
  
// Given an array term and a set of indexes return its corresponding
// scalar variable.
term_ref remove_read_visitor::get_scalar_term(term_ref array_t, 
					      const std::vector<unsigned long> &indexes,
					      const std::vector<unsigned long> &min_indexes,
					      const std::vector<unsigned long> &max_indexes) {
  
  unsigned idx = get_unidimensional_index(indexes, min_indexes, max_indexes);
  
  if (d_tm.op_of(array_t) == VARIABLE) {
    // array_t is in the CURRENT/NEXT/INPUT/PARAM set of variables.    
    arr_name_to_scalar_map::const_iterator it =
      d_arr_name_map.find(d_tm.get_variable_name(d_tm.term_of(array_t)));
    if (it != d_arr_name_map.end()) {
      const index_map_t& index_map = it->second;
      index_map_t::const_iterator iit = index_map.find(idx);
      assert(iit != index_map.end());      
      return iit->second;
    }
  }

  // build here lazily the index map for array_t
  index_map_t& index_map = d_arr_term_map[array_t];
  index_map_t::iterator it = index_map.find(idx);
  if (it != index_map.end()) {
    return it->second;
  } else {
    std::string varname = d_tm.get_fresh_variable_name();
    term_ref non_arr_var_t = d_tm.mk_variable(varname,
					      d_tm.get_array_type_element(d_tm.type_of(array_t)));
    index_map.insert(std::make_pair(idx, non_arr_var_t));
    return non_arr_var_t;
  }
}
  
static term_ref mk_and_of_eq(const std::vector<term_ref> &indexes,
			     const std::vector<unsigned long>& values, term_manager &tm) {
  assert(indexes.size() == values.size());
  std::vector<term_ref> conjuncts;
  for (unsigned i=0; i < indexes.size(); ++i) {
    rational cst(values[i]);
    conjuncts.push_back(tm.mk_term(TERM_EQ, indexes[i], tm.mk_rational_constant(cst)));
  }
  return tm.mk_and(conjuncts);
}
  
remove_read_visitor::remove_read_visitor(term_manager& tm,
					 term_to_term_map& subst_map,
					 const arr_name_to_scalar_map& arr_name_map,
					 arr_term_to_scalar_map& arr_term_map)
: d_tm(tm),
  d_subst_map(subst_map),
  d_arr_name_map(arr_name_map),
  d_arr_term_map(arr_term_map) {}

void remove_read_visitor::visit(term_ref read_t) {
  //std::cout << "VISITING read term: " << read_t << std::endl;

  if (d_tm.is_array_type(d_tm.type_of(read_t))) {
    error(d_tm, read_t, "Translation only supports fully-indexed array read terms");
  }
  
  term_ref array_t;
  std::vector<term_ref> indexes;
  std::vector<unsigned long> min_indexes, max_indexes;
  std::vector<std::vector<unsigned long> > indexes_values;

  // An array read term can have other array read terms as subterms:
  //  - indexes is the array index of each array read subterm
  //  - min_indexes contains the minimum value that an index can take  
  //  - max_indexes contains the maximum value that an index can take
  //  - array_t is the array term of the innermost select

  array_t = process_read_array(read_t, indexes, min_indexes, max_indexes);
  // After all normalization, removal of writes, read-over-ite, etc we should
  // encounter here just a variable.
  assert(d_tm.op_of(array_t) == VARIABLE);
  
  assert (indexes.size() > 0);  
  create_all_indexes_values(0, indexes, min_indexes, max_indexes, indexes_values);
  assert(indexes_values.size() > 0);
  
  if (indexes_values.size() == 1) {
    /** All indexes are constant **/         
    assert (indexes_values[0].size() == max_indexes.size());
    term_ref v = get_scalar_term(array_t, indexes_values[0], min_indexes, max_indexes);
    d_subst_map[read_t] = v;
  } else { 
    /** Some indexes are symbolic: convert the read into a nested
	ite term **/
    
    // Given (symbolic or constant) indexes [i1, 2, i3] and a
    // sequence of constant values:
    // [[c1, 2, c2], [c3, 2, c4], [c5, 2, c6], ... ]
    // it generates the term:
    // ite ((and (= i1 c1) (= i3 c3)), A_c1_2_c3,
    //    ite((and (= i1 c3) (=i3 c4)), A_c3_2_c4,
    //       ite((and (= i1 c5) (=i3 c6)), A_c5_2_c6, ....)))
    // 
    // We build the ite term starting from the two last sequence of
    // constant indexes
    std::vector<std::vector<unsigned long> >::reverse_iterator i_it, i_et;
    i_it = indexes_values.rbegin();
    i_et = indexes_values.rend();
    term_ref then_v, else_v, t;
    else_v = get_scalar_term(array_t, *i_it, min_indexes, max_indexes);
    ++i_it;
    then_v = get_scalar_term(array_t, *i_it, min_indexes, max_indexes);
    t = d_tm.mk_term(TERM_ITE, mk_and_of_eq(indexes, *i_it, d_tm), then_v, else_v);
    ++i_it;
    for (;i_it != i_et; ++i_it) {
      then_v = get_scalar_term(array_t, *i_it, min_indexes, max_indexes);
      t = d_tm.mk_term(TERM_ITE, mk_and_of_eq(indexes, *i_it, d_tm), then_v, t);
    }
    d_subst_map[read_t] = t;	
  }

  //std::cout << "TRANSLATED to: " << d_subst_map[read_t] << std::endl;
}
  
static void get_array_type_bounds_and_scalar_type(term_manager &tm, term_ref ref, 
					       std::vector<expr::utils::interval_t> &bounds,
					       term_ref &scalar_type) {
  const term& t = tm.term_of(ref);
  term_op op = t.op();
  
  if (op == TYPE_ARRAY) {
    assert (t.size () == 2);
    term_ref index_type = t[0];
    term_ref element_type = t[1];
    expr::utils::interval_t itv;
    if (expr::utils::get_bounds_from_pred_subtype(tm, index_type, itv)) {
      bounds.push_back(itv);
      // recursive
      get_array_type_bounds_and_scalar_type(tm, element_type, bounds, scalar_type); 
    } else {
      error(tm, ref, "array is not statically bounded");
    }
  } else {
    scalar_type = ref;
  }
}

/**
 Map an array variable denoted by its name and type with a bunch of
 scalar variables denoted also by their names and types. The mapping
 is recorded in arr_type_map.
**/
static void expand_array(term_manager &tm, std::string var_name, term_ref type_ref,
			 arr_name_to_scalar_type_map &arr_type_map,
			 std::vector<std::string> &scalar_names,
			 std::vector<term_ref> &scalar_types) {
  
  assert(tm.term_of(type_ref).op() == TYPE_ARRAY);
  
  std::vector<expr::utils::interval_t> bounds;
  std::vector<std::vector<integer> > instantiations;
  std::vector<std::vector<integer> >::iterator it, et;
  std::vector<unsigned long> min_indexes, max_indexes;    
  term_ref scalar_type;
  index_type_map_t &imap = arr_type_map[var_name];
  
  get_array_type_bounds_and_scalar_type(tm, type_ref, bounds, scalar_type);
  for (unsigned i=0; i< bounds.size(); ++i) {
    min_indexes.push_back(bounds[i].first.get_unsigned());
    max_indexes.push_back(bounds[i].second.get_unsigned());
  }
  expr::utils::create_all_instantiations(bounds.begin(), bounds.end(), instantiations);
  for (it = instantiations.begin(), et = instantiations.end(); it!=et; ++it){
    const std::vector<integer> &inst = *it;
    assert(!inst.empty());

    std::stringstream scalar_name(var_name);
    std::vector<unsigned long> indices;
    for (unsigned i=0; i < inst.size(); ++i) {
      unsigned long idx = inst[i].get_unsigned();
      indices.push_back(idx);
      scalar_name << "_" << idx;
    }
    unsigned key = get_unidimensional_index(indices, min_indexes, max_indexes);
    imap[key] = std::make_pair(scalar_name.str(), scalar_type);
    scalar_names.push_back(scalar_name.str());
    scalar_types.push_back(scalar_type);
  }
}

/**
 Return a new type as type_ref but all array type variables are
 replaced with scalar ones. The map arr_type_map remembers the mapping
 between array and scalar variables.
**/
term_ref remove_arrays::remove_arrays_impl::
mk_type_without_arrays(term_manager &tm, term_ref type_ref, 
		       arr_name_to_scalar_type_map &arr_type_map,
		       std::set<std::string> &orig_scalar_vars) {
  
  const term& t = tm.term_of(type_ref);
  assert(t.op() == TYPE_STRUCT);
  std::vector<std::string> new_vars;  
  std::vector<term_ref> new_types;
  for(unsigned i=0; i < tm.get_struct_type_size(t); ++i) {
    std::string field_id = tm.get_struct_type_field_id(t, i);
    term_ref field_ty = tm.get_struct_type_field_type(t, i);
    if (tm.term_of(field_ty).op () != TYPE_ARRAY) {
      new_vars.push_back(field_id);      
      new_types.push_back(field_ty);
      orig_scalar_vars.insert(field_id);
    } else {
      expand_array(tm, field_id, field_ty, arr_type_map, new_vars, new_types);
    }
  }
  return tm.mk_struct_type(new_vars, new_types);
}

/** 
 This method relates the old state variables with new state variables.
 It modifies the following maps:

 - d_arr_name_map is a map from array names to a map of indexes to scalar terms
 - d_non_arr_name_map is a map from non-array names to terms
**/
void remove_arrays::remove_arrays_impl::
mk_renaming_maps(term_manager &tm, term_ref struct_type, term_ref struct_term,
		 const system::state_type* st, system::state_type::var_class vc,
		 const arr_name_to_scalar_type_map &arr_type_map,
		 const std::set<std::string> &non_arr_vars) {
  
  unsigned struct_type_size = tm.get_struct_type_size(tm.term_of(struct_type));
  assert(struct_type_size == tm.get_struct_size(tm.term_of(struct_term)));
  name_to_term_map type_to_struct_vars_map;
  for(unsigned i=0; i < struct_type_size; ++i) {
    std::string var_name = tm.get_struct_type_field_id(tm.term_of(struct_type), i);
    term_ref var = tm.get_struct_field(tm.term_of(struct_term), i);
    type_to_struct_vars_map[var_name] = var;
    // update mapping for non-array variables
    if (non_arr_vars.count(var_name)) {
      std::string canonical_var_name(st->get_id() + "::" + st->to_string(vc) + "." + var_name);        
      d_non_arr_name_map[canonical_var_name] = var;
    }
  }
  
  // update  mapping for array variables
  for (arr_name_to_scalar_type_map::const_iterator it=arr_type_map.begin(), et=arr_type_map.end(); it!=et ; ++it) {
    std::string arr_var_name(st->get_id() + "::" + st->to_string(vc) + "." + it->first);    
    index_map_t &imap = d_arr_name_map[arr_var_name];
    const index_type_map_t &itype_map = it->second;    
    for (index_type_map_t::const_iterator iit=itype_map.begin(), iet=itype_map.end(); iit!=iet; ++iit) {
      imap.insert(std::make_pair(iit->first, type_to_struct_vars_map[iit->second.first]));
    }
  }
 }

/** 
 Create a new state type (new_st) from st by replacing arrays with
 scalars.  

 It modifies the two maps d_arr_name_map and d_non_arr_name_map that
 relate variables from old state type (st) with the new one that is
 created here (new_st).
**/  
void remove_arrays::remove_arrays_impl::mk_state_type_without_arrays(const system::state_type *st) {
  std::string st_id(d_id + "_state_type");
  term_manager &tm = d_ctx->tm();
  system::state_type::var_class vc;
  
  // variables that were already scalar before removing arrays variables.
  std::set<std::string> orig_scalar_vars;
  // map from old array variables to new scalar ones.
  arr_name_to_scalar_type_map arr_state_type_map;
  arr_name_to_scalar_type_map arr_input_type_map;
  arr_name_to_scalar_type_map arr_param_type_map;        

  // (struct) type term for state variables (current and next)
  term_ref state_type;
  // (struct) type term for inputs
  term_ref input_var;
  // (struct) type term for parameters
  term_ref param_type;

  // current variables (stored in a struct term)
  term_ref current_vars;
  // next variables (stored in a struct term)
  term_ref next_vars;
  // input variables (stored in a struct term)
  term_ref input_vars;
  // parameter variables (stored in a struct term)
  term_ref param_vars;
  
  state_type = mk_type_without_arrays(tm, st->get_state_type_var(), arr_state_type_map, orig_scalar_vars); 
  vc = system::state_type::STATE_CURRENT;    
  current_vars = tm.mk_variable(st_id + "::" + st->to_string(vc), state_type);
  mk_renaming_maps(tm, state_type, current_vars, st, vc, arr_state_type_map, orig_scalar_vars);

  vc = system::state_type::STATE_NEXT;
  next_vars = tm.mk_variable(st_id + "::" + st->to_string(vc), state_type);
  mk_renaming_maps(tm, state_type, next_vars, st, vc, arr_state_type_map, orig_scalar_vars);

  vc = system::state_type::STATE_INPUT;
  input_var = mk_type_without_arrays(tm, st->get_input_type_var(), arr_input_type_map, orig_scalar_vars);
  input_vars = tm.mk_variable(st_id + "::" + st->to_string(vc),input_var);
  mk_renaming_maps(tm, input_var, input_vars, st, vc, arr_input_type_map, orig_scalar_vars);

  vc = system::state_type::STATE_PARAM;
  param_type = mk_type_without_arrays(tm, st->get_param_type_var(), arr_param_type_map, orig_scalar_vars);
  param_vars = tm.mk_variable(st_id + "::" + st->to_string(vc), param_type);
  mk_renaming_maps(tm, param_type, param_vars, st, vc, arr_param_type_map, orig_scalar_vars);

  d_new_st = new system::state_type(st_id, tm,
				    state_type, input_var, param_type,
				    current_vars, next_vars, input_vars, param_vars);
				    
}

// We modify the state_type again to accomodate auxiliary variables
// introduced during normalization.
void remove_arrays::remove_arrays_impl::
add_state_type_variables(const std::vector<term_ref>& vars,
			 term_to_term_map& vars_map) {
  term_manager& tm = d_ctx->tm();
  
  term_ref state_type = d_new_st->get_state_type_var();
  term_ref input_type = d_new_st->get_input_type_var();
  term_ref param_type = d_new_st->get_param_type_var();
  term_ref current_st = d_new_st->get_vars_struct(system::state_type::STATE_CURRENT);
  term_ref next_st = d_new_st->get_vars_struct(system::state_type::STATE_NEXT);
  term_ref input_st = d_new_st->get_vars_struct(system::state_type::STATE_INPUT);
  term_ref param_st = d_new_st->get_vars_struct(system::state_type::STATE_PARAM);  

  term_ref new_state_type;
  term_ref new_current_st;

  // Update state_type
  const term& t = tm.term_of(state_type);
  assert(t.op() == TYPE_STRUCT);
  std::vector<std::string> names;
  std::vector<term_ref> types;
  for(unsigned i=0, e = tm.get_struct_type_size(t); i < e; ++i) {
    names.push_back(tm.get_struct_type_field_id(t, i));
    types.push_back(tm.get_struct_type_field_type(t, i));      
  }
  for (unsigned i=0, e = vars.size(); i < e; ++i) {
    assert(tm.op_of(vars[i]) == VARIABLE);
    names.push_back(tm.get_variable_name(vars[i]));
    types.push_back(tm.type_of(vars[i]));
  }
  new_state_type = tm.mk_struct_type(names, types);


  // Update current_st
  // We should also update next_t but we assume option --add-missing-step
  // will be executed later.
  std::vector<term_ref> current_children;
  current_children.assign(tm.term_begin(tm.term_of(current_st)),
  			  tm.term_end(tm.term_of(current_st)));
  for(unsigned i=0, e = vars.size(); i < e; ++i) {
    // FIXME: expose internal details of state_type
    std::string canonical = d_id + "_state_type::" +
                            d_new_st->to_string(system::state_type::STATE_CURRENT) + "." +
                            d_ctx->tm().get_variable_name(d_ctx->tm().term_of(vars[i]));
    term_ref v = d_ctx->tm().mk_variable(canonical, d_ctx->tm().type_of(vars[i])); 
					 
    current_children.push_back(v);
    vars_map[vars[i]] = v;
  }
  new_current_st = tm.get_internal()->mk_term<VARIABLE>(tm.get_variable_name(current_st) ,
  							current_children.begin(), current_children.end());
  
  // The context will own this pointer
  system::state_type * st = new system::state_type(d_id + "_state_type",
						   tm, new_state_type, input_type, param_type,
						   new_current_st, next_st, input_st, param_st);

  // free and swap pointers
  std::swap(d_new_st, st);
  delete st;
}
  

static term_ref rewrite(term_manager& tm, term_ref t,
			term_to_term_map& subst_map,
			arr_name_to_scalar_map& arr_name_map,
			arr_term_to_scalar_map& arr_term_map)  {
  term_ref res(t);
  
  /** 
      Remove all array write terms
   **/
  remove_write_terms rw(tm);
  res = rw.apply(res);

  /**
     Apply read-over-ite: pull over ite terms when children are array
     read terms
  **/
  read_over_ite roi(tm);
  res = roi.apply(res);
  
  /** 
      Remove all array read terms
   **/
  remove_read_visitor rr_visitor(tm, subst_map, arr_name_map, arr_term_map);
  term_visit_topological<remove_read_visitor, term_ref, term_ref_hasher>
    rr_visit_topological(rr_visitor);
  rr_visit_topological.run(res);
  res = tm.substitute(res, subst_map);
  return res;
}
  
remove_arrays::remove_arrays_impl::remove_arrays_impl(system::context *ctx, std::string id,
						      const system::state_type *st)
  : d_ctx(ctx), d_id(id), d_new_st(0) {
  mk_state_type_without_arrays(st);
}

/** Create a new term without arrays **/
term_ref remove_arrays::remove_arrays_impl::apply_term(term_ref t) {
  term_manager &tm = d_ctx->tm();  
  term_ref t_new = t;
  // --  we replace old non-array with new non-array variables
  t_new = expr::utils::name_substitute(tm, t_new, d_non_arr_name_map);
  // -- we replace old array with new non-array variables  
  t_new = rewrite(tm, t_new, d_subs_map, d_arr_name_map, d_arr_term_map);
  return t_new;
}

void remove_arrays::remove_arrays_impl::
apply(const system::transition_system *ts,
      const std::vector<const system::state_formula*>& queries,
      system::transition_system *& new_ts,
      std::vector<const system::state_formula*>& new_queries) {

  new_queries.clear();
  new_queries.reserve(queries.size());
  
  term_ref new_init_t = ts->get_initial_states();
  term_ref new_tr_t = ts->get_transition_relation();
  new_init_t = apply_term(new_init_t);
  new_tr_t = apply_term(new_tr_t);  

  std::vector<term_ref> new_st_formulas;
  new_st_formulas.reserve(queries.size());
  for (unsigned i=0, e=queries.size(); i < e; ++i) {
    new_st_formulas.push_back(apply_term(queries[i]->get_formula()));
  }
  /***  BEGIN AUXILIARY VARIABLES ***/
  // Important: we need to call "apply_term" exhaustively before creating
  // new transitions_system and state_formula so that we make sure we
  // include all auxiliary variables in the state type.
  // 
  // Add auxiliary variables introduced during normalization
  // 
  // -- collect auxiliary variables
  std::vector<term_ref> auxiliary_vars;
  for(arr_term_to_scalar_map::const_iterator it = d_arr_term_map.begin(),
	et = d_arr_term_map.end(); it != et; ++it) {
    const index_map_t& imap = it->second;
    for (index_map_t::const_iterator iit = imap.begin(); iit!= imap.end(); ++iit) {
      auxiliary_vars.push_back(iit->second);
    }
  }
  
  // -- add auxiliary variables in the state type
  term_to_term_map aux_vars_map;
  add_state_type_variables(auxiliary_vars, aux_vars_map);
  
  // -- rename auxiliary variables in the terms with new state type variables
  new_init_t = d_ctx->tm().substitute(new_init_t, aux_vars_map);
  new_tr_t = d_ctx->tm().substitute(new_tr_t, aux_vars_map);
  for (unsigned i=0, e=new_st_formulas.size(); i < e; ++i) {
    new_st_formulas[i] = d_ctx->tm().substitute(new_st_formulas[i], aux_vars_map);
  }
  /*** END AUXILIARY VARIABLES ***/
  
  // Finally, register the new state type in the context
  d_ctx->add_state_type(d_id, d_new_st);  

  const system::state_type* st = d_ctx->get_state_type(d_id);
  system::state_formula* new_init = new system::state_formula(d_ctx->tm(), st, new_init_t);
  system::transition_formula* new_tr = new system::transition_formula(d_ctx->tm(), st, new_tr_t);
  new_ts = new system::transition_system(st, new_init, new_tr);
  d_ctx->add_transition_system(d_id, new_ts);
  for (unsigned i=0, e = new_st_formulas.size(); i < e; ++i) {
    system::state_formula* new_sf = new system::state_formula(d_ctx->tm(), st, new_st_formulas[i]); 
    d_ctx->add_state_formula(d_id, new_sf);
    new_queries.push_back(new_sf);
  }
}
  
}
}
}
