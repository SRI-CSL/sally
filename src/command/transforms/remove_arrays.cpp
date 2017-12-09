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
typedef std::map<unsigned, term_ref> index_map_t;
typedef boost::unordered_map<std::string, index_map_t> arr_to_scalar_map;

typedef std::map<unsigned, std::pair<std::string, term_ref> > index_type_map_t;
typedef boost::unordered_map<std::string, index_type_map_t> arr_to_scalar_type_map;
typedef boost::unordered_map<std::string, term_ref> name_to_term_map;

class remove_arrays::remove_arrays_impl {

public:
  
  remove_arrays_impl(system::context *ctx, std::string id, const system::state_type *st);
  
  void apply (const system::transition_system *ts);
  
  void apply(const system::state_formula *sf);
  
private:
  
  system::context *d_ctx;
  std::string d_id;
  term_manager::substitution_map d_subs_map;
  /* map old array variables with scalar ones */
  arr_to_scalar_map d_arr_map;
  /* map old non-array variables with new renamed ones */
  name_to_term_map d_non_arr_map;

  void mk_state_type_without_arrays(const system::state_type *st);

  term_ref mk_type_var_without_arrays(term_manager &tm, term_ref type_var, 
				      arr_to_scalar_type_map &arr_type_map,
				      std::set<std::string> &orig_scalar_vars);
  
  void mk_renaming_maps(term_manager &tm, term_ref type_var, term_ref vars_struct,
			const system::state_type* st, system::state_type::var_class vc,
			const arr_to_scalar_type_map &arr_type_map,
			const std::set<std::string> &non_arr_vars);    
};
  
remove_arrays::remove_arrays(system::context *ctx, std::string id, const system::state_type *st)
  : m_pImpl(new remove_arrays_impl(ctx, id, st)) {}

remove_arrays::~remove_arrays() {
  delete m_pImpl;
}
  
void remove_arrays::apply(const system::transition_system *ts) {
  m_pImpl->apply(ts);
}
  
void remove_arrays::apply(const system::state_formula *sf){
  m_pImpl->apply(sf);
}

static void error(term_manager &tm, term_ref t_ref, std::string message) {
  std::stringstream ss;
  term_manager* _tm = output::get_term_manager(std::cerr);
  if (_tm->get_internal() == tm.get_internal()) {
    output::set_term_manager(ss, _tm);
  }
  ss << "Can't remove arrays " << t_ref;
  if (message.length() > 0) { ss << "(" << message << ")"; }
  ss << ".";
  throw exception(ss.str());
}
  
/**************************************************************************/  
/****                 Remove array write terms                        *****/
/**************************************************************************/    
class remove_write_visitor {
public:
  
  remove_write_visitor(term_manager& tm, term_to_term_map& subst_map)
  : d_tm(tm), d_subst_map(subst_map) {}
    

  // Non-null terms are good
  bool is_good_term(term_ref t) const {
    return !t.is_null();
  }

  /** Get the children of the term t that are relevant for removing
      write terms */
  void get_children(term_ref t, std::vector<term_ref>& children) {
    const term& t_term = d_tm.term_of(t);
    for (size_t i = 0; i < t_term.size(); ++ i) {
      children.push_back(t_term[i]);
    }
  }

  /** We visit only nodes that don't have types yet and are relevant
      for removing writes */
  visitor_match_result match(term_ref t) {
    if (d_tm.term_of(t).op() == TERM_ARRAY_LAMBDA ||
	d_tm.term_of(t).op() == TERM_FORALL ||
	d_tm.term_of(t).op() == TERM_EXISTS) {
      error(d_tm, t, "this term is not allowed!");
    }
    if (d_subst_map.find(t) != d_subst_map.end()) {
      // Don't visit children or this node or the node
      return DONT_VISIT_AND_BREAK;
    } else if (d_tm.term_of(t).op() == TERM_ARRAY_WRITE) {
      // We stop at the top-level array write found
      return VISIT_AND_BREAK;
    } else {
      // Don't visit this node but visit children
      return DONT_VISIT_AND_CONTINUE;    
    }
  }

  /** Visit the term (children already processed) */
  void visit(term_ref t_ref) {
  /**  TODO: remove write terms by applying:
        - [read-over-write]    
          read(write(A,i,v),j) = if i==j then v else read(A,j)
        - [(bounded) partial equalities] 
           A' = write(A,i,v) 
          forall k in [lb,ub] :: if k==i then read(A',k)
                                 else read(A',k) = read(A,k)
   **/
    error(d_tm, t_ref, " we have not implemented yet the removal of array writes");
  }
  
private:
  
  term_manager& d_tm;
  term_to_term_map& d_subst_map; 
  
};  

/**************************************************************************/  
/*                 Remove array read terms                                */
/*                                                                        */
/* Preconditions: all arrays have been expanded and no array write terms. */
/**************************************************************************/    
class remove_read_visitor {
public:
  
  remove_read_visitor(term_manager& tm, term_to_term_map& subst_map, arr_to_scalar_map& arr_map);

  // Non-null terms are good
  bool is_good_term(term_ref t) const {
    return !t.is_null();
  }

  /** Get the children of the term t that are relevant for remove read
      terms */
  void get_children(term_ref t, std::vector<term_ref>& children) {
    const term& t_term = d_tm.term_of(t);
    for (size_t i = 0; i < t_term.size(); ++ i) {
      children.push_back(t_term[i]);
    }
  }

  /** We visit only nodes that don't have types yet and are relevant
      for removing reads */
  visitor_match_result match(term_ref t) {
    if (d_tm.term_of(t).op() == TERM_ARRAY_WRITE ||
	d_tm.term_of(t).op() == TERM_ARRAY_LAMBDA ||	
	d_tm.term_of(t).op() == TERM_FORALL ||
	d_tm.term_of(t).op() == TERM_EXISTS) {
      error(d_tm, t, "this term is not allowed!");
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

  /** Visit the term (children already processed) */
  void visit(term_ref t_ref);
  
private:
  
  term_manager& d_tm;
  term_to_term_map& d_subst_map; 
  arr_to_scalar_map& d_arr_map;

  // ref is read(read(....,_),_)
  // return the array variable of the innermost read term
  term_ref get_read_array_var(term_ref ref);

  // ref is read(read(....,_),_)
  // return indexes and maximum value each index can take
  void get_read_array_indexes(term_ref ref,
			      std::vector<term_ref> &indexes,
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
				 const std::vector<unsigned long> &max_indices,
				 std::vector<std::vector<unsigned long> > &indexes_values);

  /* map an array access to array_var denoted by indexes to a scalar variable */
  term_ref get_scalar_var(term_ref array_var, 
			  const std::vector<unsigned long> &indexes,
			  const std::vector<unsigned long> &max_indexes);
};


/* Return a number N from a sequence of indexes where
  N = ((max_indices[0] * ... * max_indices[k-2]) * (indices[0] - 1)) + 
      ((max_indices[1] * ... * max_indices[k-2]) * (indices[1] - 1)) + 
      ((max_indices[2] * ... * max_indices[k-2]) * (indices[2] - 1)) + 
      ...
      (max_indices[k-2]                   * (indices[k-2]-1)) + 
      indices[k-1]
*/
static unsigned get_unidimensional_index(const std::vector<unsigned long> &indices,
					 const std::vector<unsigned long> &max_indices) {
  assert (indices.size() > 0);
  assert (indices.size() == max_indices.size());
  unsigned r = 0;
  unsigned k = indices.size();  
  for (unsigned i=0; i < k; ++i) {
    unsigned v = 1;
    for (unsigned j=i; j < k-1; ++j) {
      v *= max_indices[j];
    }
      r += (v * ((i==k-1 ? indices[i] : indices[i] -1)));
  }
  return r;
}
      
term_ref remove_read_visitor::get_read_array_var(term_ref ref) {
  if (d_tm.op_of(ref) == TERM_ARRAY_READ) {
    term_ref a = d_tm.get_array_read_array(ref);
    return get_read_array_var(a); // recursive
  }
  if (d_tm.op_of(ref) != VARIABLE) {
    error(d_tm, ref, "read array can be only either a nested array read or variable");
  }
  return ref;
}

void remove_read_visitor::get_read_array_indexes(term_ref ref,
						 std::vector<term_ref> &indexes,
						 std::vector<unsigned long> &max_indexes) {
  if (d_tm.op_of(ref) == TERM_ARRAY_READ) {
    term_ref a = d_tm.get_array_read_array(ref);
    term_ref i = d_tm.get_array_read_index(ref);
    term_ref i_ty = d_tm.get_array_type_index(d_tm.type_of(a));
    expr::utils::interval_t itv;    
    if (expr::utils::get_bounds_from_pred_subtype(d_tm, i_ty, itv)) {
      unsigned long lb = itv.first.get_unsigned();
      unsigned long ub = itv.second.get_unsigned();
      if (lb != 1) {
	error(d_tm, ref, "array term must be indexed from 1");
      }
      get_read_array_indexes(a, indexes, max_indexes);  // recursive
      // XXX: important to return the transformed version of the index
      indexes.push_back(d_tm.substitute(i, d_subst_map));
      max_indexes.push_back(ub);
    } else {
      error(d_tm, ref, "array is not statically bounded");
    }
  } else {
    if (d_tm.op_of(ref) != VARIABLE) {
      error(d_tm, ref, "read array can be only either a nested array read or variable");
    }
  }
}
    
/** TODO: non-recursive **/
void remove_read_visitor::create_all_indexes_values(unsigned i,
						    const std::vector<term_ref> &indices,
						    const std::vector<unsigned long> &max_indices,
						    std::vector<std::vector<unsigned long> > &indexes_values) {
  if (i < indices.size()) {
    unsigned long max_index = max_indices[i];
    integer ind; 
    bool is_constant_index = expr::utils::term_to_integer(d_tm, indices[i], ind);
    unsigned long constant_index = 0;
    if (is_constant_index) {
      constant_index = ind.get_unsigned();
      max_index = 1;
    }
    create_all_indexes_values(++i, indices, max_indices, indexes_values);
    
    if (indexes_values.empty()) {
      for (unsigned long j=1; j <= max_index; ) {
	std::vector<unsigned long> singleton;
	singleton.push_back((is_constant_index ? constant_index : j));
	indexes_values.push_back(singleton);
	j = j + 1;
      }
    } else {
      std::vector<std::vector<unsigned long> > new_indexes_values;      
      for (unsigned long j = 1 ; j <= max_index; ) {
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
  
    
term_ref remove_read_visitor::get_scalar_var(term_ref array_var, 
					     const std::vector<unsigned long> &indexes,
					     const std::vector<unsigned long> &max_indexes) {
  unsigned idx = get_unidimensional_index(indexes, max_indexes);
  index_map_t &index_map = d_arr_map[d_tm.get_variable_name(d_tm.term_of(array_var))];
  index_map_t::iterator it = index_map.find(idx);
  if (it != index_map.end()) {
    return it->second;
  } else {    
    error(d_tm, array_var, "cannot map array variable");
    return term_ref();
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
					 arr_to_scalar_map& arr_map)
: d_tm(tm),
  d_subst_map(subst_map),
  d_arr_map(arr_map) {}

void remove_read_visitor::visit(term_ref read_t) {
  term_ref array_var;
  std::vector<term_ref> indexes;
  std::vector<unsigned long> max_indexes;
  std::vector<std::vector<unsigned long> > indexes_values;

  // An array term can have other array terms as subterms:
  //  - indexes is the array index of each array read subterm    
  //  - max_indexes contains the maximum value that an index can take
  //  - array_var is the array variable of the innermost select
  get_read_array_indexes(read_t, indexes, max_indexes);
  array_var = get_read_array_var(read_t);
  assert (indexes.size() > 0);  
  create_all_indexes_values(0, indexes, max_indexes, indexes_values);
  assert(indexes_values.size() > 0);
  
  if (indexes_values.size() == 1) {
    /** All indexes are constant **/         
    assert (indexes_values[0].size() == max_indexes.size());
    term_ref v = get_scalar_var(array_var, indexes_values[0], max_indexes);
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
    else_v = get_scalar_var(array_var, *i_it, max_indexes);
    ++i_it;
    then_v = get_scalar_var(array_var, *i_it, max_indexes);
    t = d_tm.mk_term(TERM_ITE, mk_and_of_eq(indexes, *i_it, d_tm), then_v, else_v);
    ++i_it;
    for (;i_it != i_et; ++i_it) {
      then_v = get_scalar_var(array_var, *i_it, max_indexes);
      t = d_tm.mk_term(TERM_ITE, mk_and_of_eq(indexes, *i_it, d_tm), then_v, t);
    }
    d_subst_map[read_t] = t;	
  }
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
      unsigned long lb = itv.first.get_unsigned();
      if (lb != 1) {
	error(tm, ref, "array term must be indexed from 1");
      }
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
			 arr_to_scalar_type_map &arr_type_map,
			 std::vector<std::string> &scalar_names,
			 std::vector<term_ref> &scalar_types) {
  
  assert(tm.term_of(type_ref).op() == TYPE_ARRAY);
  
  std::vector<expr::utils::interval_t> bounds;
  std::vector<std::vector<integer> > instantiations;
  std::vector<std::vector<integer> >::iterator it, et;
  std::vector<unsigned long> max_indexes;    
  term_ref scalar_type;
  index_type_map_t &imap = arr_type_map[var_name];
  
  get_array_type_bounds_and_scalar_type(tm, type_ref, bounds, scalar_type);
  for (unsigned i=0; i< bounds.size(); ++i) {
    max_indexes.push_back(bounds[i].second.get_unsigned());
  }
  expr::utils::create_all_instantiations(bounds.begin(), bounds.end(), instantiations);
  for (it = instantiations.begin(), et = instantiations.end(); it!=et; ++it){
    const std::vector<integer> &inst = *it;
    assert(!inst.empty());

    std::string scalar_name(var_name);
    std::vector<unsigned long> indices;
    for (unsigned i=0; i < inst.size(); ++i) {
      unsigned long idx = inst[i].get_unsigned();
      indices.push_back(idx);
      scalar_name += "_" + std::to_string(idx);
    }
    unsigned key = get_unidimensional_index(indices, max_indexes);
    imap[key] = std::make_pair(scalar_name, scalar_type);
    scalar_names.push_back(scalar_name);
    scalar_types.push_back(scalar_type);
  }
}

/**
 Return a new type variable as type_var but all array type variables
 are replace with scalar ones. The map arr_type_map remembers the
 mapping between array and scalar variables.
**/
term_ref remove_arrays::remove_arrays_impl::
mk_type_var_without_arrays(term_manager &tm, term_ref type_var, 
			   arr_to_scalar_type_map &arr_type_map,
			   std::set<std::string> &orig_scalar_vars) {
  
  const term& t = tm.term_of(type_var);
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
 This method relates the old state variables with new state variables 
 - d_arr_map is a map from array names to a map of indexes to scalar terms
 - d_non_arr_map is a map from non-array names to terms
**/
void remove_arrays::remove_arrays_impl::
mk_renaming_maps(term_manager &tm, term_ref type_var, term_ref vars_struct,
		 const system::state_type* st, system::state_type::var_class vc,
		 const arr_to_scalar_type_map &arr_type_map,
		 const std::set<std::string> &non_arr_vars) {
  
  unsigned type_var_size = tm.get_struct_type_size(tm.term_of(type_var));
  assert(type_var_size == tm.get_struct_size(tm.term_of(vars_struct)));
  name_to_term_map type_to_struct_vars_map;
  for(unsigned i=0; i < type_var_size; ++i) {
    std::string var_name = tm.get_struct_type_field_id(tm.term_of(type_var), i);
    term_ref var = tm.get_struct_field(tm.term_of(vars_struct), i);
    type_to_struct_vars_map[var_name] = var;
    
    // update mapping for non-array variables
    if (non_arr_vars.count(var_name)) {
      std::string canonical_var_name(st->get_id() + "::" + st->to_string(vc) + "." + var_name);        
      d_non_arr_map[canonical_var_name] = var;
    }
  }
  
  // update  mapping for array variables
  for (arr_to_scalar_type_map::const_iterator it=arr_type_map.begin(), et=arr_type_map.end(); it!=et ; ++it) {
    std::string arr_var_name(st->get_id() + "::" + st->to_string(vc) + "." + it->first);    
    index_map_t &imap = d_arr_map[arr_var_name];
    const index_type_map_t &itype_map = it->second;    
    for (index_type_map_t::const_iterator iit=itype_map.begin(), iet=itype_map.end(); iit!=iet; ++iit) {
      imap.insert(std::make_pair(iit->first, type_to_struct_vars_map[iit->second.first]));
    }
  }
 }

/** 
 Create a new state type (new_st) from st by replacing arrays with
 scalars.  It also produces two maps (d_arr_map and d_non_arr_map)
 that relate variables from old state type (st) with the new one that
 is created here (new_st).
**/  
void remove_arrays::remove_arrays_impl::mk_state_type_without_arrays(const system::state_type *st) {
  std::string st_id(d_id + "_state_type");
  term_manager &tm = d_ctx->tm();
  system::state_type::var_class vc;
  
  // variables that were already scalar before removing arrays variables.
  std::set<std::string> orig_scalar_vars;
  // map from old array variables to new scalar ones.
  arr_to_scalar_type_map arr_state_type_map;
  
  term_ref state_type_var = mk_type_var_without_arrays(tm, st->get_state_type_var(), 
						       arr_state_type_map, orig_scalar_vars);
  vc = system::state_type::STATE_CURRENT;
  term_ref current_vars_struct = tm.mk_variable(st_id + "::" + st->to_string(vc), state_type_var);
  mk_renaming_maps(tm, state_type_var, current_vars_struct, st, vc, arr_state_type_map, orig_scalar_vars);

  vc = system::state_type::STATE_NEXT;
  term_ref next_vars_struct = tm.mk_variable(st_id + "::" + st->to_string(vc), state_type_var);
  mk_renaming_maps(tm, state_type_var, next_vars_struct, st, vc, arr_state_type_map, orig_scalar_vars);

  vc = system::state_type::STATE_INPUT;
  arr_to_scalar_type_map arr_input_type_map;      
  term_ref input_type_var = mk_type_var_without_arrays(tm, st->get_input_type_var(),
						       arr_input_type_map, orig_scalar_vars);
  term_ref input_vars_struct = tm.mk_variable(st_id + "::" + st->to_string(vc),input_type_var);
  mk_renaming_maps(tm, input_type_var, input_vars_struct, st, vc, arr_input_type_map, orig_scalar_vars);

  vc = system::state_type::STATE_PARAM;
  arr_to_scalar_type_map arr_param_type_map;        
  term_ref param_type_var = mk_type_var_without_arrays(tm, st->get_param_type_var(),
						       arr_param_type_map, orig_scalar_vars);
  term_ref param_vars_struct = tm.mk_variable(st_id + "::" + st->to_string(vc), param_type_var);
  mk_renaming_maps(tm, param_type_var, param_vars_struct, st, vc, arr_param_type_map, orig_scalar_vars);

  system::state_type *new_st = new system::state_type(st_id, tm, state_type_var, input_type_var, param_type_var,
						      current_vars_struct, next_vars_struct,
						      input_vars_struct, param_vars_struct);
  
  d_ctx->add_state_type(d_id, new_st);
}

static term_ref rewrite(term_manager& tm, term_ref t,
			term_to_term_map &subst_map, arr_to_scalar_map &arr_map)  {
  term_ref res(t);
  
  { // remove first all write terms
    typedef remove_write_visitor visitor_t;    
    visitor_t visitor(tm, subst_map);
    term_visit_topological<visitor_t, term_ref, term_ref_hasher> visit_topological(visitor);
    visit_topological.run(res);
    res = tm.substitute(res, subst_map);
  }

  { // and then all read terms
    typedef remove_read_visitor visitor_t;
    visitor_t visitor(tm, subst_map, arr_map);
    term_visit_topological<visitor_t, term_ref, term_ref_hasher> visit_topological(visitor);
    visit_topological.run(res);
    res = tm.substitute(t, subst_map);
  }
  
  return res;
}
  
remove_arrays::remove_arrays_impl::remove_arrays_impl(system::context *ctx, std::string id,
						      const system::state_type *st)
: d_ctx(ctx), d_id(id) {
  mk_state_type_without_arrays(st);
}
    
/** Create a new transition system but without arrays **/  
void remove_arrays::remove_arrays_impl::apply(const system::transition_system *ts) {
  if (!d_ctx->has_state_type(d_id)) {
    std::stringstream ss;
    term_manager* tm = output::get_term_manager(std::cerr);
    if (tm->get_internal() == d_ctx->tm().get_internal()) {
      output::set_term_manager(ss, tm);
    }
    ss << "Can't remove arrays ";
    ss << "(no state type found for Id " << d_id << ")";
    throw exception(ss.str());
  }
  term_manager &tm = d_ctx->tm();
  term_ref init, tr, new_init, new_tr;
    
  init = ts->get_initial_states();
  tr = ts->get_transition_relation();

  // --  we replace old non-array with new non-array variables
  init = expr::utils::name_substitute(tm, init, d_non_arr_map);
  tr = expr::utils::name_substitute(tm, tr, d_non_arr_map);  
  // -- we replace old array with new non-array variables
  new_init = rewrite(tm,init,d_subs_map, d_arr_map);
  new_tr = rewrite(tm,tr,d_subs_map, d_arr_map);
  const system::state_type* st = d_ctx->get_state_type(d_id);  
  system::state_formula* new_init_f = new system::state_formula(tm, st, new_init);
  system::transition_formula* new_tr_f = new system::transition_formula(tm, st, new_tr);
  system::transition_system* new_ts = new system::transition_system(st, new_init_f, new_tr_f);
  d_ctx->add_transition_system(d_id, new_ts);
}
  
/** Create a new state formula but without arrays **/    
void remove_arrays::remove_arrays_impl::apply(const system::state_formula *sf){
  if (!d_ctx->has_state_type(d_id)) {
    std::stringstream ss;
    term_manager* tm = output::get_term_manager(std::cerr);
    if (tm->get_internal() == d_ctx->tm().get_internal()) {
      output::set_term_manager(ss, tm);
    }
    ss << "Can't remove arrays ";
    ss << "(no state type found for Id " << d_id << ")";
    throw exception(ss.str());
  }
  term_manager &tm = d_ctx->tm();
  term_ref f, new_f;

  f = sf->get_formula();
  // --  we replace old non-array with new non-array variables
  f = expr::utils::name_substitute(tm, f, d_non_arr_map);
  // -- we replace old array with new non-array variables  
  new_f = rewrite(tm,f,d_subs_map, d_arr_map);
  const system::state_type* st = d_ctx->get_state_type(d_id);  
  system::state_formula * new_sf = new system::state_formula(tm, st, new_f);  
  d_ctx->add_state_formula(d_id, new_sf);
}


}
}
}
