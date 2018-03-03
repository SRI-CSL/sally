#include "expr/term_manager_internal.h"
#include "expr/term_manager.h"
#include "expr/term_visitor.h"

#include "inlining.h"
//#include "term_utils.h"
//#include <boost/unordered_map.hpp>
#include <iostream>
//#include <vector>

namespace sally {
namespace system {
namespace transforms {

using namespace expr;

inliner::inliner(context* ctx, const transition_system* original)
: transform(ctx, original)
{
  // TODO: just a blueprint, doing nothing
  d_transformed = new transition_system(original);
}

state_formula* inliner::apply(const state_formula* f_state, direction D) {
  // TODO
  return new state_formula(f_state);
}

transition_formula* inliner::apply(const transition_formula* f_trans, direction D) {
  // TODO
  return new transition_formula(f_trans);
}

expr::model::ref inliner::apply(expr::model::ref model, direction d) {
  // TODO
  return model;
}

// TODO: Remove all below

inliner::inliner(const transition_system* original, context *ctx, std::string id, const state_type *st)
: transform(ctx, original)
{}

void inliner::apply(const transition_system *ts,
    const std::vector<const state_formula*>& queries,
    transition_system*& new_ts,
    std::vector<const state_formula*>& new_queries) {
  // NOOP for now to be able to run regressions
  new_ts = const_cast<transition_system*>(ts);
  for (size_t i = 0; i < queries.size(); ++ i) {
    new_queries.push_back(queries[i]);
  }
}


}
}
}
