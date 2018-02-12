#include "expr/term_manager_internal.h"
#include "expr/term_manager.h"
#include "expr/term_visitor.h"

#include "remove_enum_types.h"
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
  
class remove_enum_types::remove_enum_types_impl {

public:
  
  remove_enum_types_impl(system::context *ctx, std::string id, const system::state_type *st);
  
  void apply (const system::transition_system* ts,
	      const std::vector<const system::state_formula*>& queries,
	      system::transition_system*& new_ts,
	      std::vector<const system::state_formula*>& new_queries);
private:
  
  system::context *d_ctx;
  std::string d_id;
  // map variable names to terms
  name_to_term_map d_name_to_term_map;
  // map CONST_ENUM values to CONST_RATIONAL values
  term_to_term_map d_subs_map;  

  void mk_state_type_without_enum_types(const system::state_type *st);
  term_ref mk_type_var_without_enum_types(term_manager &tm, term_ref type_var,
					const system::state_type *st, system::state_type::var_class vc);
  void mk_renaming_map(term_manager &tm, term_ref type_var, term_ref vars_struct,
		       const system::state_type* st, system::state_type::var_class vc);

  system::transition_system* apply (const system::transition_system *ts);
  system::state_formula* apply(const system::state_formula *sf);
  
};
  
remove_enum_types::remove_enum_types(const system::transition_system* original, system::context *ctx, std::string id, const system::state_type *st)
  : transform(original), m_pImpl(new remove_enum_types_impl(ctx, id, st)) {}

remove_enum_types::~remove_enum_types() {
  delete m_pImpl;
}

system::state_formula* remove_enum_types::apply(const system::state_formula* f_state, direction D) {
  // TODO
  assert(false);
  return 0;
}

system::transition_formula* remove_enum_types::apply(const system::transition_formula* f_trans, direction D) {
  // TODO
  assert(false);
  return 0;
}

expr::model::ref remove_enum_types::apply(expr::model::ref model, direction d) {
  // TODO
  assert(false);
  return model;
}

void remove_enum_types::apply(const system::transition_system* ts,
			      const std::vector<const system::state_formula*>& queries,
			      system::transition_system*& new_ts,
			      std::vector<const system::state_formula*>& new_queries){
  m_pImpl->apply(ts, queries, new_ts, new_queries);
}
  
/** 
 This function relates the old state variables with new state variables 
**/
void remove_enum_types::remove_enum_types_impl::
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
 Return a new type variable as type_var but all enum types are
 replaced with an integer type.
**/
term_ref remove_enum_types::remove_enum_types_impl::
mk_type_var_without_enum_types(term_manager &tm, term_ref type_var,
			       const system::state_type* st, system::state_type::var_class vc) {
  const term& t = tm.term_of(type_var);
  assert(t.op() == TYPE_STRUCT);
  std::vector<std::string> new_vars;  
  std::vector<term_ref> new_types;
  for(unsigned i=0; i < tm.get_struct_type_size(t); ++i) {
    std::string field_id = tm.get_struct_type_field_id(t, i);
    term_ref field_ty = tm.get_struct_type_field_type(t, i);
    if (tm.term_of(field_ty).op () != TYPE_ENUM) {
      new_vars.push_back(field_id);      
      new_types.push_back(field_ty);
    } else {
      size_t enum_size = tm.get_enum_type_size(field_ty);
      for (unsigned j=0; j < enum_size; ++j) {
	assert(tm.term_of(tm.term_of(field_ty)[j]).op() == CONST_STRING);
	/** 
	    JN: tm.term_of(field_ty)[j] is an enum value and
	    therefore, it should be CONST_ENUM.  However, the SAL
	    parser produces a CONST_STRING. I think the parser should
	    be fixed.  Meanwhile, we create a new CONST_ENUM with the
	    same value that the CONST_STRING.
	**/
	std::string const_name = tm.get_string_constant(tm.term_of(tm.term_of(field_ty)[j]));
	term_ref enum_val = tm.mk_enum_constant(const_name, field_ty);
	term_ref idx = tm.mk_rational_constant(rational(j+1));
	d_subs_map[enum_val] = idx;
      }
      new_vars.push_back(field_id);
      // new type for field_id is {x in INT | x >= 1 AND x <= enum_size}
      term_ref var = tm.mk_variable(tm.integer_type());
      term_ref body = tm.mk_and(tm.mk_term(TERM_GEQ, var, tm.mk_rational_constant(rational(1))),
				tm.mk_term(TERM_LEQ, var, tm.mk_rational_constant(rational(enum_size))));
      term_ref new_field_ty = tm.mk_predicate_subtype(var, body);
      new_types.push_back(new_field_ty);
      d_subs_map[field_ty] = new_field_ty;
    }
  }
  return tm.mk_struct_type(new_vars, new_types);
}
  
/** 
 Create a new state type (new_st) from st.
**/  
void remove_enum_types::remove_enum_types_impl::mk_state_type_without_enum_types(const system::state_type *st) {
  term_manager &tm = d_ctx->tm();  
  std::string st_id(d_id + "_state_type");
  system::state_type::var_class vc;

  vc = system::state_type::STATE_CURRENT;
  term_ref state_type_var = mk_type_var_without_enum_types(tm, st->get_state_type_var(), st, vc);
  term_ref current_vars_struct = tm.mk_variable(st_id + "::" + st->to_string(vc), state_type_var);
  mk_renaming_map(tm, state_type_var, current_vars_struct, st, vc);

  vc = system::state_type::STATE_NEXT;
  term_ref next_vars_struct = tm.mk_variable(st_id + "::" + st->to_string(vc), state_type_var);
  mk_renaming_map(tm, state_type_var, next_vars_struct, st, vc);

  vc = system::state_type::STATE_INPUT;  
  term_ref input_type_var = mk_type_var_without_enum_types(tm, st->get_input_type_var(), st, vc);
  term_ref input_vars_struct = tm.mk_variable(st_id + "::" + st->to_string(vc),input_type_var);
  mk_renaming_map(tm, input_type_var, input_vars_struct, st, vc);

  vc = system::state_type::STATE_PARAM;    
  term_ref param_type_var = mk_type_var_without_enum_types(tm, st->get_param_type_var(), st, vc);
  term_ref param_vars_struct = tm.mk_variable(st_id + "::" + st->to_string(vc), param_type_var);
  mk_renaming_map(tm, param_type_var, param_vars_struct, st, vc);

  system::state_type *new_st = new system::state_type(st_id, tm, state_type_var, input_type_var, param_type_var,
  						      current_vars_struct, next_vars_struct,
						      input_vars_struct, param_vars_struct);
  d_ctx->add_state_type(d_id, new_st);
}

remove_enum_types::remove_enum_types_impl::remove_enum_types_impl(system::context *ctx, std::string id,
								  const system::state_type *st)
: d_ctx(ctx), d_id(id)
{
  mk_state_type_without_enum_types(st);
}
  
/** Create a new transition system but without enum types **/  
system::transition_system* remove_enum_types::remove_enum_types_impl::apply(const system::transition_system *ts) {
  if (!d_ctx->has_state_type(d_id)) {
    std::stringstream ss;
    term_manager* tm = output::get_term_manager(std::cerr);
    if (tm->get_internal() == d_ctx->tm().get_internal()) {
      output::set_term_manager(ss, tm);
    }
    ss << "Can't remove enum type ";
    ss << "(no state type found for Id " << d_id << ")";
    throw exception(ss.str());
  }
  term_manager &tm = d_ctx->tm();
  term_ref init, tr, new_init, new_tr;
  
  init = ts->get_initial_states();
  tr = ts->get_transition_relation();

  new_init = expr::utils::name_substitute(tm, init, d_name_to_term_map);
  new_init = tm.substitute(new_init, d_subs_map);
  
  new_tr = expr::utils::name_substitute(tm, tr, d_name_to_term_map);
  new_tr =  tm.substitute(new_tr, d_subs_map);
  
  const system::state_type* st = d_ctx->get_state_type(d_id);  
  system::state_formula* new_init_f = new system::state_formula(tm, st, new_init);
  system::transition_formula* new_tr_f = new system::transition_formula(tm, st, new_tr);
  system::transition_system* new_ts = new system::transition_system(st, new_init_f, new_tr_f);

  d_ctx->add_transition_system(d_id, new_ts);
  return new_ts;
}

/** Create a new state formula but without enum types **/    
system::state_formula* remove_enum_types::remove_enum_types_impl::apply(const system::state_formula *sf){
  if (!d_ctx->has_state_type(d_id)) {
    std::stringstream ss;
    term_manager* tm = output::get_term_manager(std::cerr);
    if (tm->get_internal() == d_ctx->tm().get_internal()) {
      output::set_term_manager(ss, tm);
    }
    ss << "Can't remove enum types ";
    ss << "(no state type found for Id " << d_id << ")";
    throw exception(ss.str());
  }

  term_manager &tm = d_ctx->tm();  
  term_ref f, new_f;
  
  f = sf->get_formula();
  new_f = expr::utils::name_substitute(tm, f, d_name_to_term_map);
  new_f = tm.substitute(new_f, d_subs_map);
  
  const system::state_type* st = d_ctx->get_state_type(d_id);  
  system::state_formula * new_sf = new system::state_formula(tm, st, new_f);
  d_ctx->add_state_formula(d_id, new_sf);
  return new_sf;
}

void remove_enum_types::remove_enum_types_impl::apply(const system::transition_system *ts,
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
