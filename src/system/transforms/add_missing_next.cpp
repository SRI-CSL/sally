#include "add_missing_next.h"
#include "term_utils.h"

#include <iostream>
#include <set>

namespace sally {
namespace system {
namespace transforms {

using namespace expr;

add_missing_next::add_missing_next(const transition_system* original, context *ctx, std::string id)
: transform(ctx, original), d_id(id)
{}

add_missing_next::add_missing_next(context *ctx, const transition_system* original)
: transform(ctx, original)
{
  term_manager& tm = d_ctx->tm();
  const state_type* st = original->get_state_type();
  term_ref tr = original->get_transition_relation();

  // Get all the next variables as a set
  const std::vector<term_ref>& next_vec = st->get_variables(state_type::STATE_NEXT);
  std::set<term_ref> next_set(next_vec.begin(), next_vec.end());

  // Get all variables in transition relation
  std::set<term_ref> all_tr_vars;
  tm.get_variables(tr, all_tr_vars);

  // Get all variables in next but not in transition relation
  std::set<term_ref> missed_next;
  std::set_difference(next_set.begin(), next_set.end(),
                      all_tr_vars.begin(), all_tr_vars.end(),
                      std::inserter(missed_next, missed_next.begin()));

  // Construct x' = x for all variables in missed_next
  std::vector<term_ref> equalities;
  for (std::set<term_ref>::const_iterator it = missed_next.begin(), et = missed_next.end(); it != et; ++it) {
    term_ref next = *it;
    term_ref curr = st->change_formula_vars(state_type::STATE_NEXT, state_type::STATE_CURRENT, next);
    equalities.push_back(tm.mk_term(TERM_EQ, next, curr));
  }

  // Construct the new system
  state_formula* new_init = new state_formula(tm, st, original->get_initial_states());
  transition_formula* new_tr = new transition_formula(tm, st, tm.mk_and(tr, tm.mk_and(equalities)));
  transition_system* new_ts = new transition_system(st, new_init, new_tr);

  // Record the system
  d_transformed = new_ts;
}

state_formula* add_missing_next::apply(const state_formula* f_state, direction D) {
  // We don't change state type, so formula stays the same
  return new state_formula(f_state);
}

transition_formula* add_missing_next::apply(const transition_formula* f_trans, direction D) {
  // We don't change state type so formula stays the same
  return new transition_formula(f_trans);
}

expr::model::ref add_missing_next::apply(expr::model::ref model, direction d) {
  // We don't change state type so model stays the same
  return model;
}

static transition_system* apply_ts(context* ctx, std::string id, const transition_system *ts) {

  term_manager &tm = ctx->tm();  
  const state_type* st = ts->get_state_type();
  term_ref tr = ts->get_transition_relation();

  const std::vector<term_ref>& next_vars_v = st->get_variables(state_type::STATE_NEXT);
  std::set<term_ref> next_vars(next_vars_v.begin(), next_vars_v.end());
  
  std::set<term_ref> all_tr_vars;
  tm.get_variables(tr, all_tr_vars);

  std::set<term_ref> missed_next;
  std::set_difference(next_vars.begin(), next_vars.end(),
		      all_tr_vars.begin(), all_tr_vars.end(),
		      std::inserter(missed_next, missed_next.begin()));
  
  // missed_next are the next variables which are not mentioned in the
  // transition relation.
  std::vector<term_ref> equalities;
  for (std::set<term_ref>::iterator it = missed_next.begin(), et = missed_next.end(); it != et; ++it) {
    term_ref next = *it;
    term_ref curr = st->change_formula_vars(state_type::STATE_NEXT,
					    state_type::STATE_CURRENT,
					    next);
    //std::cout << "ADD " << next << " = " << curr << std::endl;
    equalities.push_back(tm.mk_term(TERM_EQ, next, curr));
  }
  term_ref new_tr = tm.mk_and(tr, tm.mk_and(equalities));
  
  state_formula* new_init_t = new state_formula(tm, st, ts->get_initial_states());
  transition_formula* new_tr_f = new transition_formula(tm, st, new_tr);

  transition_system* new_ts = new transition_system(st, new_init_t, new_tr_f);
  ctx->add_transition_system(id, new_ts);
  return new_ts;
}
  
static state_formula* apply_sf(context* ctx, const state_formula *sf) {
  term_manager& tm = ctx->tm();  
  const state_type* st = sf->get_state_type();
  state_formula* new_sf = new state_formula(tm, st, sf->get_formula());
  return new_sf;
}
  
void add_missing_next::apply(const transition_system *ts,
			     const std::vector<const state_formula*>& queries,
			     transition_system *& new_ts,
			     std::vector<const state_formula*>& new_queries) {
  
  new_ts = apply_ts(d_ctx, d_id, ts);
  new_queries.clear();
  new_queries.reserve(queries.size());
  for (std::vector<const state_formula*>::const_iterator it = queries.begin(),
	 et = queries.end(); it!=et; ++it) {
    new_queries.push_back(apply_sf(d_ctx, *it));
  }
  
}
  
}
}
}
