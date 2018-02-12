#include "expr/term_manager_internal.h"
#include "expr/term_manager.h"
#include "expr/term_visitor.h"

#include "remove_subtypes.h"
#include "term_utils.h"

#include <boost/unordered_map.hpp>
#include <iostream>
#include <vector>

namespace sally {
namespace cmd {
namespace transforms {

using namespace expr;
  
typedef term_manager::substitution_map term_to_term_map;
typedef boost::unordered_map<std::string, term_ref> name_to_term_map;

struct assumption {
  term_manager* d_tm;
  // -- the formula
  term_ref d_f;
  // -- the lambda var (i.e., f is defined only over v)
  term_ref d_v;

  assumption(term_manager *tm, term_ref f, term_ref v)
    : d_tm(tm), d_f(f), d_v(v){}

  term_ref replace(term_ref v) {
    term_to_term_map subs_map;
    subs_map[d_v] = v;
    return d_tm->substitute(d_f, subs_map);
  }
};
  
typedef boost::unordered_map<std::string, assumption> assumption_map;  
  
class remove_subtypes::remove_subtypes_impl {

public:
  
  remove_subtypes_impl(system::context *ctx, std::string id, const system::state_type *st);
  
  void apply (const system::transition_system* ts,
	      const std::vector<const system::state_formula*>& queries,
	      system::transition_system*& new_ts,
	      std::vector<const system::state_formula*>& new_queries);
  
private:
  
  system::context *d_ctx;
  std::string d_id;
  name_to_term_map d_name_to_term_map;
  assumption_map d_assumptions;

  void mk_state_type_without_subtypes(const system::state_type *st);
  term_ref mk_type_var_without_subtypes(term_manager &tm, term_ref type_var,
					const system::state_type *st, system::state_type::var_class vc);
  void mk_renaming_map(term_manager &tm, term_ref type_var, term_ref vars_struct,
		       const system::state_type* st, system::state_type::var_class vc);
  void add_assumptions(term_manager &tm, system::transition_system* ts);

  system::transition_system* apply (const system::transition_system *ts);
  system::state_formula* apply(const system::state_formula *sf);
  
};
  
remove_subtypes::remove_subtypes(const system::transition_system* original, system::context *ctx, std::string id, const system::state_type *st)
  : transform(original), m_pImpl(new remove_subtypes_impl(ctx, id, st)) {}

remove_subtypes::~remove_subtypes() {
  delete m_pImpl;
}

system::state_formula* remove_subtypes::apply(const system::state_formula* f_state, direction D) {
  // TODO
  assert(false);
  return 0;
}

system::transition_formula* remove_subtypes::apply(const system::transition_formula* f_trans, direction D) {
  // TODO
  assert(false);
  return 0;
}

expr::model::ref remove_subtypes::apply(expr::model::ref model, direction d) {
  // TODO
  assert(false);
  return model;
}

void remove_subtypes::apply (const system::transition_system* ts,
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
  ss << "Can't remove predicate subtype " << t_ref;
  if (message.length() > 0) { ss << ". " << message; }
  ss << ".";
  throw exception(ss.str());
}
  
/** 
 This function relates the old state variables with new state variables 
**/
void remove_subtypes::remove_subtypes_impl::
mk_renaming_map(term_manager &tm, term_ref type_var, term_ref vars_struct,
		const system::state_type* st, system::state_type::var_class vc) {
  
  unsigned type_var_size = tm.get_struct_type_size(tm.term_of(type_var));
  assert(type_var_size == tm.get_struct_size(tm.term_of(vars_struct)));
  for(unsigned i=0; i < type_var_size; ++i) {
    std::string var_name = tm.get_struct_type_field_id(tm.term_of(type_var), i);
    term_ref var = tm.get_struct_field(tm.term_of(vars_struct), i);
    std::string old_var_name = st->get_canonical_name(var_name, vc);
    d_name_to_term_map[old_var_name] = var;
  }
}
  
/**
 Return a new type variable as type_var but all predicate subtype type
 variables are replaced with the type of the subtype variable.
**/
term_ref remove_subtypes::remove_subtypes_impl::
mk_type_var_without_subtypes(term_manager &tm, term_ref type_var,
			     const system::state_type* st, system::state_type::var_class vc) {
  const term& t = tm.term_of(type_var);
  assert(t.op() == TYPE_STRUCT);
  std::vector<std::string> new_vars;  
  std::vector<term_ref> new_types;
  for(unsigned i=0; i < tm.get_struct_type_size(t); ++i) {
    std::string field_id = tm.get_struct_type_field_id(t, i);
    term_ref field_ty = tm.get_struct_type_field_type(t, i);
    if (tm.term_of(field_ty).op () != TYPE_PREDICATE_SUBTYPE) {
      new_vars.push_back(field_id);      
      new_types.push_back(field_ty);
    } else {
      term_ref var = tm.get_predicate_subtype_variable(field_ty);
      if (tm.term_of(tm.type_of(var)).op() >= TYPE_BOOL && tm.term_of(tm.type_of(var)).op() <= TYPE_REAL) {
	new_vars.push_back(field_id);
	new_types.push_back(tm.type_of(var));
	// -- Record assumption
	if (vc == system::state_type::STATE_CURRENT || vc == system::state_type::STATE_PARAM) {
	  std::string old_var_name = st->get_canonical_name(field_id, vc);
	  term_ref body = tm.get_predicate_subtype_body(field_ty);
	  //std::cout << "Assumption " << var << " --- " << body << std::endl;
	  assumption a(&tm, body, var);
	  d_assumptions.insert(std::make_pair(old_var_name, a));
	}
      } else {
	error(tm, field_ty, "support only for bool, integer, or real");
      }
    }
  }
  return tm.mk_struct_type(new_vars, new_types);
}
  
/** 
 Create a new state type (new_st) from st by replacing subtypes with
 subtype variable's type.
**/  
void remove_subtypes::remove_subtypes_impl::mk_state_type_without_subtypes(const system::state_type *st) {
  term_manager &tm = d_ctx->tm();  
  std::string st_id(d_id + "_state_type");
  system::state_type::var_class vc;


  vc = system::state_type::STATE_CURRENT;
  term_ref state_type_var = mk_type_var_without_subtypes(tm, st->get_state_type_var(), st, vc);
  term_ref current_vars_struct = tm.mk_variable(st_id + "::" + st->to_string(vc), state_type_var);
  mk_renaming_map(tm, state_type_var, current_vars_struct, st, vc);

  vc = system::state_type::STATE_NEXT;
  term_ref next_vars_struct = tm.mk_variable(st_id + "::" + st->to_string(vc), state_type_var);
  mk_renaming_map(tm, state_type_var, next_vars_struct, st, vc);

  vc = system::state_type::STATE_INPUT;  
  term_ref input_type_var = mk_type_var_without_subtypes(tm, st->get_input_type_var(), st, vc);
  term_ref input_vars_struct = tm.mk_variable(st_id + "::" + st->to_string(vc),input_type_var);
  mk_renaming_map(tm, input_type_var, input_vars_struct, st, vc);

  vc = system::state_type::STATE_PARAM;    
  term_ref param_type_var = mk_type_var_without_subtypes(tm, st->get_param_type_var(), st, vc);
  term_ref param_vars_struct = tm.mk_variable(st_id + "::" + st->to_string(vc), param_type_var);
  mk_renaming_map(tm, param_type_var, param_vars_struct, st, vc);

  system::state_type *new_st = new system::state_type(st_id, tm, state_type_var, input_type_var, param_type_var,
  						      current_vars_struct, next_vars_struct,
						      input_vars_struct, param_vars_struct);
  d_ctx->add_state_type(d_id, new_st);
}

void remove_subtypes::remove_subtypes_impl::add_assumptions(term_manager &tm, system::transition_system* ts) {
  const system::state_type* st = ts->get_state_type();
  
  // build a map from param names to their terms
  name_to_term_map param_name_to_term_map;
  const std::vector<term_ref>& param_type_vars = st->get_variables(system::state_type::STATE_PARAM);
  for (std::vector<term_ref>::const_iterator it = param_type_vars.begin(), et=param_type_vars.end(); it!=et ; ++it) {
    param_name_to_term_map[tm.get_variable_name(*it)] = *it;
  }
  
  for (assumption_map::iterator it = d_assumptions.begin() , et = d_assumptions.end(); it != et; ++it) {
    term_ref sf = (it->second).replace(d_name_to_term_map[it->first]);

    // Rename param type variables in safe with state variable This is
    // possible when a predicate subtype uses some constants defined
    // as param variables.
    std::vector<term_ref> sf_vars;
    tm.get_variables(sf, sf_vars);
    term_to_term_map param_subs_map;
    for (std::vector<term_ref>::const_iterator v_it = sf_vars.begin(), v_et=sf_vars.end(); v_it!=v_et ; ++v_it){
      std::string name = st->get_canonical_name(tm.get_variable_name(*v_it),
						system::state_type::STATE_PARAM);
      name_to_term_map::const_iterator nt_it = param_name_to_term_map.find(name);
      if (nt_it != param_name_to_term_map.end()) {
     	param_subs_map[*v_it] = nt_it->second;
	//std::cout << "replace " << *v_it << " with " << nt_it->second << std::endl;
      }
    }
    sf = tm.substitute(sf, param_subs_map);
    ts->add_assumption(new system::state_formula(tm, st, sf));    
  }
}
  
remove_subtypes::remove_subtypes_impl::remove_subtypes_impl(system::context *ctx, std::string id,
							    const system::state_type *st)
: d_ctx(ctx), d_id(id) {
  mk_state_type_without_subtypes(st);
}
    
/** Create a new transition system but without subtypes **/  
system::transition_system* remove_subtypes::remove_subtypes_impl::apply(const system::transition_system *ts) {
  if (!d_ctx->has_state_type(d_id)) {
    std::stringstream ss;
    term_manager* tm = output::get_term_manager(std::cerr);
    if (tm->get_internal() == d_ctx->tm().get_internal()) {
      output::set_term_manager(ss, tm);
    }
    ss << "Can't remove subtypes ";
    ss << "(no state type found for Id " << d_id << ")";
    throw exception(ss.str());
  }
  term_manager &tm = d_ctx->tm();
  term_ref init, tr, new_init, new_tr;
  
  init = ts->get_initial_states();
  tr = ts->get_transition_relation();
  new_init = expr::utils::name_substitute(tm, init, d_name_to_term_map);
  new_tr = expr::utils::name_substitute(tm, tr, d_name_to_term_map);

  const system::state_type* st = d_ctx->get_state_type(d_id);  
  system::state_formula* new_init_f = new system::state_formula(tm, st, new_init);
  system::transition_formula* new_tr_f = new system::transition_formula(tm, st, new_tr);
  system::transition_system* new_ts = new system::transition_system(st, new_init_f, new_tr_f);

  add_assumptions(tm, new_ts);
  d_ctx->add_transition_system(d_id, new_ts);
  return new_ts;
}

/** Create a new state formula but without subtypes **/    
system::state_formula* remove_subtypes::remove_subtypes_impl::apply(const system::state_formula *sf){
  if (!d_ctx->has_state_type(d_id)) {
    std::stringstream ss;
    term_manager* tm = output::get_term_manager(std::cerr);
    if (tm->get_internal() == d_ctx->tm().get_internal()) {
      output::set_term_manager(ss, tm);
    }
    ss << "Can't remove subtypes ";
    ss << "(no state type found for Id " << d_id << ")";
    throw exception(ss.str());
  }

  term_manager &tm = d_ctx->tm();  
  term_ref f, new_f;  
  f = sf->get_formula();
  new_f = expr::utils::name_substitute(tm, f, d_name_to_term_map);  
  const system::state_type* st = d_ctx->get_state_type(d_id);  
  system::state_formula * new_sf = new system::state_formula(tm, st, new_f);
  d_ctx->add_state_formula(d_id, new_sf);
  return new_sf;
}

void remove_subtypes::remove_subtypes_impl::apply(const system::transition_system *ts,
						  const std::vector<const system::state_formula*>& queries,
						  system::transition_system *& new_ts,
						  std::vector<const system::state_formula*>& new_queries) {
  new_ts = apply(ts);
  new_queries.clear();
  new_queries.reserve(queries.size());
  for (std::vector<const system::state_formula*>::const_iterator it = queries.begin(),
	 et = queries.end(); it!=et; ++it) {
    new_queries.push_back(apply(*it));
  }
  
}


}
}
}
