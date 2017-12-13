#include "expr/term_manager_internal.h"
#include "expr/term_manager.h"
#include "expr/term_visitor.h"

#include "promote_nonstate_to_state.h"
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
  
class promote_nonstate_to_state::promote_nonstate_to_state_impl {

public:
  
  promote_nonstate_to_state_impl(system::context *ctx, std::string id, const system::state_type *st);
  
  system::transition_system* apply (const system::transition_system *ts);
  
  system::state_formula* apply(const system::state_formula *sf);
  
private:
  
  system::context *d_ctx;
  std::string d_id;
  // map variable names to terms
  name_to_term_map d_name_to_term_map;
};
  
promote_nonstate_to_state::promote_nonstate_to_state(system::context *ctx, std::string id, const system::state_type *st)
  : m_pImpl(new promote_nonstate_to_state_impl(ctx, id, st)) {}

promote_nonstate_to_state::~promote_nonstate_to_state() {
  delete m_pImpl;
}
  
system::transition_system* promote_nonstate_to_state::apply(const system::transition_system *ts) {
  return m_pImpl->apply(ts);
}
  
system::state_formula* promote_nonstate_to_state::apply(const system::state_formula *sf){
  return m_pImpl->apply(sf);
}
  
promote_nonstate_to_state::promote_nonstate_to_state_impl::
promote_nonstate_to_state_impl(system::context *ctx, std::string id, const system::state_type *st)
: d_ctx(ctx), d_id(id)
{
  /** 
     Create a new state type (new_st) from st where param variables are
     promoted to state variables.
     FIXME: factorize code, otherwise it's hard to mantain.
  **/  
  
  term_manager &tm = d_ctx->tm();  
  std::string st_id(d_id + "_state_type");
  system::state_type::var_class vc;

  std::vector<std::string> names;  
  std::vector<term_ref> types;
  term_ref state_type_var, param_type_var, input_type_var;
  term_ref current_vars_struct, next_vars_struct, param_vars_struct, input_vars_struct;
  
  // -- Merge param + state current type vars
  const term& t1= tm.term_of(st->get_state_type_var());
  for(unsigned i=0; i < tm.get_struct_type_size(t1); ++i) {
    names.push_back(tm.get_struct_type_field_id(t1, i));      
    types.push_back(tm.get_struct_type_field_type(t1, i));
  }    
  const term& t2= tm.term_of(st->get_param_type_var());
  for(unsigned i=0; i < tm.get_struct_type_size(t2); ++i) {
    names.push_back(tm.get_struct_type_field_id(t2, i));      
    types.push_back(tm.get_struct_type_field_type(t2, i));
  }
  
  state_type_var = tm.mk_struct_type(names, types);
  current_vars_struct = tm.mk_variable(st_id + "::" + st->to_string(system::state_type::STATE_CURRENT), state_type_var);
  
  // -- create map between old state names (state_type_var) and new
  //    variables (current_vars_struct)
  unsigned state_type_var_size = tm.get_struct_type_size(tm.term_of(state_type_var));
  for(unsigned i=0; i < state_type_var_size; ++i) {
    std::string var_name = tm.get_struct_type_field_id(tm.term_of(state_type_var), i);
    vc = (i < tm.get_struct_type_size(t1) ? system::state_type::STATE_CURRENT : system::state_type::STATE_PARAM);
    var_name = st->get_canonical_name(var_name, vc);    
    term_ref var = tm.get_struct_field(tm.term_of(current_vars_struct), i);
    d_name_to_term_map[var_name] = var;
  }
  
  // -- Merge param + state next type vars
  next_vars_struct = tm.mk_variable(st_id + "::" + st->to_string(system::state_type::STATE_NEXT), state_type_var);

  // -- create map between old state names (state_type_var) and new
  //    variables (next_vars_struct).
  for(unsigned i=0; i < tm.get_struct_type_size(t1); ++i) { // we don't go again through param 
    std::string var_name = tm.get_struct_type_field_id(tm.term_of(state_type_var), i);
    var_name = st->get_canonical_name(var_name, system::state_type::STATE_NEXT);    
    term_ref var = tm.get_struct_field(tm.term_of(next_vars_struct), i);
    d_name_to_term_map[var_name] = var;
  }

  // Empty param type vars
  names.clear(); types.clear();
  param_type_var = tm.mk_struct_type(names, types);
  param_vars_struct = tm.mk_variable(st_id + "::" + st->to_string(system::state_type::STATE_PARAM), param_type_var);

  // We don't promote input variables to state variables
  names.clear(); types.clear();  
  const term& t3= tm.term_of(st->get_input_type_var());
  for(unsigned i=0; i < tm.get_struct_type_size(t3); ++i) {
    names.push_back(tm.get_struct_type_field_id(t3, i));      
    types.push_back(tm.get_struct_type_field_type(t3, i));
  }    
  input_type_var = tm.mk_struct_type(names, types);
  input_vars_struct = tm.mk_variable(st_id + "::" + st->to_string(system::state_type::STATE_INPUT), input_type_var);
  // -- create map between old state names (input_type_var) and new variables (input_vars_struct)
  unsigned input_type_var_size = tm.get_struct_type_size(tm.term_of(input_type_var));
  for(unsigned i=0; i < input_type_var_size; ++i) {
    std::string var_name = tm.get_struct_type_field_id(tm.term_of(input_type_var), i);
    var_name = st->get_canonical_name(var_name, system::state_type::STATE_INPUT);    
    term_ref var = tm.get_struct_field(tm.term_of(input_vars_struct), i);
    d_name_to_term_map[var_name] = var;
  }
  
  system::state_type *new_st = new system::state_type(st_id, tm, state_type_var, input_type_var, param_type_var,
  						      current_vars_struct, next_vars_struct,
						      input_vars_struct, param_vars_struct);
  d_ctx->add_state_type(d_id, new_st);
}
  
system::transition_system * promote_nonstate_to_state::promote_nonstate_to_state_impl::
apply(const system::transition_system *ts) {
  if (!d_ctx->has_state_type(d_id)) {
    std::stringstream ss;
    term_manager* tm = output::get_term_manager(std::cerr);
    if (tm->get_internal() == d_ctx->tm().get_internal()) {
      output::set_term_manager(ss, tm);
    }
    ss << "Can't promote non-state to state variables ";
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

  d_ctx->add_transition_system(d_id, new_ts);
  return new_ts;
}

system::state_formula* promote_nonstate_to_state::promote_nonstate_to_state_impl::
apply(const system::state_formula *sf){
  if (!d_ctx->has_state_type(d_id)) {
    std::stringstream ss;
    term_manager* tm = output::get_term_manager(std::cerr);
    if (tm->get_internal() == d_ctx->tm().get_internal()) {
      output::set_term_manager(ss, tm);
    }
    ss << "Can't promote non-state to state variables ";
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


}
}
}
