#include "promote_params_to_state.h"

#include "expr/term_manager_internal.h"
#include "expr/term_manager.h"
#include "expr/term_visitor.h"

#include "system/context.h"
#include "system/state_formula.h"
#include "system/transition_formula.h"
#include "system/transition_system.h"

#include "term_utils.h"

#include <boost/unordered_map.hpp>
#include <iostream>
#include <vector>

namespace sally {
namespace system {
namespace transforms {

using namespace expr;
  
typedef term_manager::substitution_map substitution_map;
typedef boost::unordered_map<std::string, term_ref> name_to_term_map;

promote_params_to_state::promote_params_to_state(context* ctx, const transition_system* original)
: transform(ctx, original), m_pImpl(0)
{
  // Original info
  const state_type* original_state_type = original->get_state_type();

  // Names and types of the variables to make new state (state + param)
  std::vector<std::string> state_names;
  std::vector<term_ref> state_types;
  tm().get_struct_type_elements(original_state_type->get_state_type_var(), state_names, state_types);
  tm().get_struct_type_elements(original_state_type->get_param_type_var(), state_names, state_types);

  // Elements of the new state
  term_ref state_type_var = tm().mk_struct_type(state_names, state_types);
  term_ref input_type_var = original_state_type->get_input_type_var();
  std::vector<std::string> empty_names;
  std::vector<term_ref> empty_types;
  term_ref param_type_var = tm().mk_struct_type(empty_names, empty_types);

  // Make the new state type
  std::string fresh_id = d_ctx->get_fresh_id(original_state_type->get_id());
  state_type* transformed_state_type = new state_type(fresh_id, tm(), state_type_var, input_type_var, param_type_var);
  d_ctx->add_state_type(fresh_id, transformed_state_type);

  typedef std::vector<expr::term_ref> term_ref_vec;

  // Variables in the original state type
  const term_ref_vec& state_vars = original_state_type->get_variables(state_type::STATE_CURRENT);
  const term_ref_vec& input_vars = original_state_type->get_variables(state_type::STATE_INPUT);
  const term_ref_vec& next_vars  = original_state_type->get_variables(state_type::STATE_NEXT);
  const term_ref_vec& param_vars = original_state_type->get_variables(state_type::STATE_PARAM);

  // Variables in the transformed state type
  const term_ref_vec& transformed_state_vars = transformed_state_type->get_variables(state_type::STATE_CURRENT);
  const term_ref_vec& transformed_input_vars = transformed_state_type->get_variables(state_type::STATE_INPUT);
  const term_ref_vec& transformed_next_vars  = transformed_state_type->get_variables(state_type::STATE_NEXT);

  // Make a substitution map from old vars to new vars
  for (size_t i = 0; i < state_vars.size(); ++ i) {
    d_substitution_map[state_vars[i]] = transformed_state_vars[i];
  }
  for (size_t i = 0; i < input_vars.size(); ++ i) {
    d_substitution_map[input_vars[i]] = transformed_input_vars[i];
  }
  for (size_t i = 0; i < next_vars.size(); ++ i) {
    d_substitution_map[next_vars[i]] = transformed_next_vars[i];
  }
  for (size_t i = 0; i < param_vars.size(); ++ i) {
    d_substitution_map[param_vars[i]] = transformed_state_vars[i + state_vars.size()];
  }

  // Create the new transition system
  term_ref init = tm().substitute(original->get_initial_states(), d_substitution_map);
  term_ref trans = tm().substitute(original->get_transition_relation(), d_substitution_map);
  d_transformed = new transition_system(transformed_state_type,
      new state_formula(tm(), transformed_state_type, init),
      new transition_formula(tm(), transformed_state_type, trans));
}

state_formula* promote_params_to_state::apply(const state_formula* f_state, direction D) {
  assert(D = TRANSFORM_FORWARD);
  const state_type* transformed_state_type = d_transformed->get_state_type();
  term_ref transformed_f = tm().substitute(f_state->get_formula(), d_substitution_map);
  return new state_formula(tm(), transformed_state_type, transformed_f);
}

transition_formula* promote_params_to_state::apply(const transition_formula* f_trans, direction D) {
  assert(D = TRANSFORM_FORWARD);
  const state_type* transformed_state_type = d_transformed->get_state_type();
  term_ref transformed_f = tm().substitute(f_trans->get_formula(), d_substitution_map);
  return new transition_formula(tm(), transformed_state_type, transformed_f);
}

expr::model::ref promote_params_to_state::apply(expr::model::ref model, direction D) {
  assert(D == TRANSFORM_FORWARD);
  return model->rename_variables(d_substitution_map);
}

class promote_params_to_state::promote_nonstate_to_state_impl {

public:
  
  promote_nonstate_to_state_impl(context *ctx, std::string id, const state_type *st);
  
  void apply(const transition_system* ts,
	     const std::vector<const state_formula*>& queries,
	     transition_system*& new_ts,
	     std::vector<const state_formula*>& new_queries);
  
private:
  
  context *d_ctx;
  std::string d_id;
  // map variable names to terms
  name_to_term_map d_name_to_term_map;
  std::vector<term_ref> d_promoted_vars;

  transition_system* apply (const transition_system *ts);
  state_formula* apply(const state_formula *sf);
  
};
  
promote_params_to_state::promote_params_to_state(const transition_system* original, context *ctx, std::string id, const state_type *st)
  : transform(ctx, original), m_pImpl(new promote_nonstate_to_state_impl(ctx, id, st)) {}

promote_params_to_state::~promote_params_to_state() {
  delete m_pImpl;
}
  
void promote_params_to_state::apply(const transition_system* ts,
					const std::vector<const state_formula*>& queries,
					transition_system*& new_ts,
					std::vector<const state_formula*>& new_queries) {
  m_pImpl->apply(ts, queries, new_ts, new_queries);
}
    
promote_params_to_state::promote_nonstate_to_state_impl::
promote_nonstate_to_state_impl(context *ctx, std::string id, const state_type *st)
: d_ctx(ctx), d_id(id)
{
  /** 
     Create a new state type (new_st) from st where PARAM variables are
     promoted to state variables.
     FIXME: factorize code, otherwise it's hard to mantain.
  **/  
  
  term_manager &tm = d_ctx->tm();  
  std::string st_id(d_id + "_state_type");
  state_type::var_class vc;

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
  current_vars_struct = tm.mk_variable(st_id + "::" + st->to_string(state_type::STATE_CURRENT), state_type_var);

  // -- create map between old state names (state_type_var) and new
  //    variables (current_vars_struct)
  unsigned state_type_var_size = tm.get_struct_type_size(tm.term_of(state_type_var));
  for(unsigned i=0; i < state_type_var_size; ++i) {
    std::string var_name = tm.get_struct_type_field_id(tm.term_of(state_type_var), i);
    vc = (i < tm.get_struct_type_size(t1) ? state_type::STATE_CURRENT : state_type::STATE_PARAM);
    var_name = st->get_canonical_name(var_name, vc);    
    term_ref var = tm.get_struct_field(tm.term_of(current_vars_struct), i);
    d_name_to_term_map[var_name] = var;
    if (i >= tm.get_struct_type_size(t1)) {
      d_promoted_vars.push_back(var);
    }
  }
  
  // -- Merge param + state next type vars
  next_vars_struct = tm.mk_variable(st_id + "::" + st->to_string(state_type::STATE_NEXT), state_type_var);

  // -- create map between old state names (state_type_var) and new
  //    variables (next_vars_struct).
  for(unsigned i=0; i < tm.get_struct_type_size(t1); ++i) { // we don't go again through param 
    std::string var_name = tm.get_struct_type_field_id(tm.term_of(state_type_var), i);
    var_name = st->get_canonical_name(var_name, state_type::STATE_NEXT);
    term_ref var = tm.get_struct_field(tm.term_of(next_vars_struct), i);
    d_name_to_term_map[var_name] = var;
  }

  // Empty param type vars
  names.clear(); types.clear();
  param_type_var = tm.mk_struct_type(names, types);
  param_vars_struct = tm.mk_variable(st_id + "::" + st->to_string(state_type::STATE_PARAM), param_type_var);

  // We don't promote input variables to state variables
  names.clear(); types.clear();  
  const term& t3= tm.term_of(st->get_input_type_var());
  for(unsigned i=0; i < tm.get_struct_type_size(t3); ++i) {
    names.push_back(tm.get_struct_type_field_id(t3, i));      
    types.push_back(tm.get_struct_type_field_type(t3, i));
  }    
  input_type_var = tm.mk_struct_type(names, types);
  input_vars_struct = tm.mk_variable(st_id + "::" + st->to_string(state_type::STATE_INPUT), input_type_var);
  // -- create map between old state names (input_type_var) and new variables (input_vars_struct)
  unsigned input_type_var_size = tm.get_struct_type_size(tm.term_of(input_type_var));
  for(unsigned i=0; i < input_type_var_size; ++i) {
    std::string var_name = tm.get_struct_type_field_id(tm.term_of(input_type_var), i);
    var_name = st->get_canonical_name(var_name, state_type::STATE_INPUT);
    term_ref var = tm.get_struct_field(tm.term_of(input_vars_struct), i);
    d_name_to_term_map[var_name] = var;
  }
  
  state_type *new_st = new state_type(st_id, tm, state_type_var, input_type_var, param_type_var,
  						      current_vars_struct, next_vars_struct,
						      input_vars_struct, param_vars_struct);
  d_ctx->add_state_type(d_id, new_st);
}
  
transition_system * promote_params_to_state::promote_nonstate_to_state_impl::
apply(const transition_system *ts) {
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

  const state_type* st = d_ctx->get_state_type(d_id);
  
  // -- connect the promoted variables with their next versions
  std::vector<term_ref> equalities;
  for (std::vector<term_ref>::iterator it = d_promoted_vars.begin(), et = d_promoted_vars.end(); it != et; ++it) {
    term_ref curr = *it;
    term_ref next = st->change_formula_vars(state_type::STATE_CURRENT,
					    state_type::STATE_NEXT,
					    curr);
    //std::cout << "ADD " << next << " = " << curr << std::endl;
    equalities.push_back(tm.mk_term(TERM_EQ, next, curr));
  }
  new_tr = tm.mk_and(new_tr, tm.mk_and(equalities));
  
  state_formula* new_init_f = new state_formula(tm, st, new_init);
  transition_formula* new_tr_f = new transition_formula(tm, st, new_tr);
  transition_system* new_ts = new transition_system(st, new_init_f, new_tr_f);

  d_ctx->add_transition_system(d_id, new_ts);
  return new_ts;
}

state_formula* promote_params_to_state::promote_nonstate_to_state_impl::
apply(const state_formula *sf){
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
  
  const state_type* st = d_ctx->get_state_type(d_id);
  state_formula * new_sf = new state_formula(tm, st, new_f);
  d_ctx->add_state_formula(d_id, new_sf);
  return new_sf;
}

void promote_params_to_state::promote_nonstate_to_state_impl::
apply(const transition_system *ts,
      const std::vector<const state_formula*>& queries,
      transition_system *& new_ts,
      std::vector<const state_formula*>& new_queries) {
  
  new_ts = apply(ts);
  new_queries.clear();
  new_queries.reserve(queries.size());
  for (std::vector<const state_formula*>::const_iterator it = queries.begin(),
	 et = queries.end(); it!=et; ++it) {
    new_queries.push_back(apply(*it));
  }
  
}
  
}
}
}
