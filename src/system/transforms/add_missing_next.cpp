#include "add_missing_next.h"
#include "term_utils.h"

#include <iostream>
#include <set>

namespace sally {
namespace cmd {
namespace transforms {

using namespace expr;
  
add_missing_next::add_missing_next(system::context *ctx, std::string id)
: d_ctx(ctx), d_id(id) {}

static system::transition_system* apply_ts(system::context* ctx, std::string id, const system::transition_system *ts) {

  term_manager &tm = ctx->tm();  
  const system::state_type* st = ts->get_state_type();
  term_ref tr = ts->get_transition_relation();

  const std::vector<term_ref>& next_vars_v = st->get_variables(system::state_type::STATE_NEXT);
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
    term_ref curr = st->change_formula_vars(system::state_type::STATE_NEXT,
					    system::state_type::STATE_CURRENT,
					    next);
    //std::cout << "ADD " << next << " = " << curr << std::endl;
    equalities.push_back(tm.mk_term(TERM_EQ, next, curr));
  }
  term_ref new_tr = tm.mk_and(tr, tm.mk_and(equalities));
  
  system::state_formula* new_init_t = new system::state_formula(tm, st, ts->get_initial_states());
  system::transition_formula* new_tr_f = new system::transition_formula(tm, st, new_tr);

  system::transition_system* new_ts = new system::transition_system(st, new_init_t, new_tr_f);
  ctx->add_transition_system(id, new_ts);
  return new_ts;
}
  
static system::state_formula* apply_sf(system::context* ctx, const system::state_formula *sf) {
  term_manager& tm = ctx->tm();  
  const system::state_type* st = sf->get_state_type();  
  system::state_formula* new_sf = new system::state_formula(tm, st, sf->get_formula());
  return new_sf;
}
  
void add_missing_next::apply(const system::transition_system *ts,
			     const std::vector<const system::state_formula*>& queries,
			     system::transition_system *& new_ts,
			     std::vector<const system::state_formula*>& new_queries) {
  
  new_ts = apply_ts(d_ctx, d_id, ts);
  new_queries.clear();
  new_queries.reserve(queries.size());
  for (std::vector<const system::state_formula*>::const_iterator it = queries.begin(),
	 et = queries.end(); it!=et; ++it) {
    new_queries.push_back(apply_sf(d_ctx, *it));
  }
  
}
  
}
}
}
