#include "expr/term_manager_internal.h"
#include "expr/term_manager.h"
#include "expr/term_visitor.h"

#include "inlining.h"
//#include "term_utils.h"
//#include <boost/unordered_map.hpp>
#include <iostream>
//#include <vector>

namespace sally {
namespace cmd {
namespace transforms {

using namespace expr;
  
//typedef term_manager::substitution_map term_to_term_map;
//typedef boost::unordered_map<std::string, term_ref> name_to_term_map;
  
static void error(term_manager &tm, term_ref t_ref, std::string message) {
  std::stringstream ss;
  term_manager* _tm = output::get_term_manager(std::cerr);
  if (_tm->get_internal() == tm.get_internal()) {
    output::set_term_manager(ss, _tm);
  }
  ss << "Can't inline function applications " << t_ref;
  if (message.length() > 0) { ss << "(" << message << ")"; }
  ss << ".";
  throw exception(ss.str());
}

class inliner::inliner_impl {

public:
  
  inliner_impl(system::context *ctx, std::string id, const system::state_type *st);
  
  system::transition_system* apply (const system::transition_system *ts);
  
  system::state_formula* apply(const system::state_formula *sf);

private:
  
  system::context *d_ctx;
  std::string d_id;
  
};
  
inliner::inliner(system::context *ctx, std::string id, const system::state_type *st)
  : m_pImpl(new inliner_impl(ctx, id, st)) {}

inliner::~inliner() {
  delete m_pImpl;
}
  
system::transition_system* inliner::apply(const system::transition_system *ts) {
  return m_pImpl->apply(ts);
}
  
system::state_formula* inliner::apply(const system::state_formula *sf){
  return m_pImpl->apply(sf);
}


class check_no_func_app_visitor {
public:
  
  check_no_func_app_visitor(term_manager& tm): d_tm(tm) {}

  // Non-null terms are good
  bool is_good_term(term_ref t) const {
    return !t.is_null();
  }

  void get_children(term_ref t, std::vector<term_ref>& children) {
    const term& t_term = d_tm.term_of(t);
    for (size_t i = 0; i < t_term.size(); ++ i) {
      children.push_back(t_term[i]);
    }
  }

  visitor_match_result match(term_ref t) {
    if (d_tm.term_of(t).op() == TERM_FUN_APP) {
      // We stop at the top-level array write found
      return VISIT_AND_BREAK;
    } else {
      // Don't visit this node but visit children
      return DONT_VISIT_AND_CONTINUE;    
    }
  }

  /** Visit the term (children already processed) */
  void visit(term_ref t_ref) {
    error(d_tm, t_ref, " we have not implemented yet inlining of function applications");
  }
  
private:
  
  term_manager& d_tm;
};  


  
inliner::inliner_impl::inliner_impl(system::context *ctx, std::string id,
				    const system::state_type */*st*/)
: d_ctx(ctx), d_id(id)
{
}

// sanity check: the term does not have function applications
static void check_no_func_app(term_manager& tm, term_ref t) {
  typedef check_no_func_app_visitor visitor_t;    
  visitor_t visitor(tm);
  term_visit_topological<visitor_t, term_ref, term_ref_hasher> visit_topological(visitor);
  visit_topological.run(t);
}
				
  
/** Create a new transition system but function applications **/  
system::transition_system* inliner::inliner_impl::apply(const system::transition_system *ts) {

  term_manager &tm = d_ctx->tm();  
  term_ref init = ts->get_initial_states();
  term_ref tr = ts->get_transition_relation();

  check_no_func_app(tm, init);
  check_no_func_app(tm, tr);
  
  /* TODO: inline function applications in init and tr */

  const system::state_type* st = ts->get_state_type();  
  system::state_formula* new_init_f = new system::state_formula(tm, st, init);
  system::transition_formula* new_tr_f = new system::transition_formula(tm, st, tr);
  system::transition_system* new_ts = new system::transition_system(st, new_init_f, new_tr_f);
  d_ctx->add_transition_system(d_id, new_ts);  
  return new_ts;
}

/** Create a new state formula but function applications **/    
system::state_formula* inliner::inliner_impl::apply(const system::state_formula *sf){

  term_manager &tm = d_ctx->tm();  
  term_ref f = sf->get_formula();

  check_no_func_app(tm, f);
    
  /* TODO: inline functions in f */
  
  const system::state_type* st = sf->get_state_type();  
  system::state_formula * new_sf = new system::state_formula(tm, st, f);
  d_ctx->add_state_formula(d_id, new_sf);
  return new_sf;  
}


}
}
}
