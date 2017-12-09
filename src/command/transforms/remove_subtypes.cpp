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
  
  void apply (const system::transition_system *ts);
  
  void apply(const system::state_formula *sf);
  
private:
  
  system::context *d_ctx;
  std::string d_id;
  name_to_term_map d_subs_map;
  term_to_term_map d_term_subs_map;  
  assumption_map d_assumptions;

  void mk_state_type_without_subtypes(const system::state_type *st);
  term_ref mk_type_var_without_subtypes(term_manager &tm, term_ref type_var,
					const system::state_type *st, system::state_type::var_class vc);
  void mk_renaming_map(term_manager &tm, term_ref type_var, term_ref vars_struct,
		       const system::state_type* st, system::state_type::var_class vc);
  void add_assumptions(term_manager &tm, system::transition_system* ts);
};
  
remove_subtypes::remove_subtypes(system::context *ctx, std::string id, const system::state_type *st)
  : m_pImpl(new remove_subtypes_impl(ctx, id, st)) {}

remove_subtypes::~remove_subtypes() {
  delete m_pImpl;
}
  
void remove_subtypes::apply(const system::transition_system *ts) {
  m_pImpl->apply(ts);
}
  
void remove_subtypes::apply(const system::state_formula *sf){
  m_pImpl->apply(sf);
}

static void error(term_ref t_ref, term_manager &tm, std::string message) {
  std::stringstream ss;
  term_manager* _tm = output::get_term_manager(std::cerr);
  if (_tm->get_internal() == tm.get_internal()) {
    output::set_term_manager(ss, _tm);
  }

  ss << message;
  if (!t_ref.is_null()) {
    ss << " (" << t_ref << ")";
  }
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
    d_subs_map[old_var_name] = var;
  }
}
  
/**
 Return a new type variable as type_var but all predicate subtype type
 variables are replace with the type of the subtype variable.
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
	  assumption a(&tm, body, var);
	  d_assumptions.insert(std::make_pair(old_var_name, a));
	}
      } else {
	error(field_ty, tm, "Can't remove predicate subtype if different from bool, integer, or real");
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
  for (assumption_map::iterator it = d_assumptions.begin() , et = d_assumptions.end(); it != et; ++it) {
    term_ref sf = (it->second).replace(d_subs_map[it->first]);
    ts->add_assumption(new system::state_formula(tm, st, sf));    
  }
}
  
remove_subtypes::remove_subtypes_impl::remove_subtypes_impl(system::context *ctx, std::string id,
							    const system::state_type *st)
: d_ctx(ctx), d_id(id) {
  mk_state_type_without_subtypes(st);
}
    
/** Create a new transition system but without subtypes **/  
void remove_subtypes::remove_subtypes_impl::apply(const system::transition_system *ts) {
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
  new_init = expr::utils::name_substitute(tm, init, d_subs_map);
  new_tr = expr::utils::name_substitute(tm, tr, d_subs_map);

  const system::state_type* st = d_ctx->get_state_type(d_id);  
  system::state_formula* new_init_f = new system::state_formula(tm, st, new_init);
  system::transition_formula* new_tr_f = new system::transition_formula(tm, st, new_tr);
  system::transition_system* new_ts = new system::transition_system(st, new_init_f, new_tr_f);

  add_assumptions(tm, new_ts);
  d_ctx->add_transition_system(d_id, new_ts);
}

/** Create a new state formula but without subtypes **/    
void remove_subtypes::remove_subtypes_impl::apply(const system::state_formula *sf){
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
  new_f = expr::utils::name_substitute(tm, f, d_subs_map);  
  const system::state_type* st = d_ctx->get_state_type(d_id);  
  system::state_formula * new_sf = new system::state_formula(tm, st, new_f);
  d_ctx->add_state_formula(d_id, new_sf);
  
}


}
}
}
