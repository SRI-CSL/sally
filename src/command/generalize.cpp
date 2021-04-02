#include "generalize.h"

#include "smt/factory.h"
#include "system/state_type.h"

#include <iostream>

namespace sally {
namespace cmd {

generalize::generalize(system::state_formula* F,
    const std::vector<expr::term_ref>& variables,
    const std::vector<expr::term_ref>& values,
    const std::vector<expr::term_ref>& vars_to_eliminate)
: command(GENERALIZE)
, d_F(F)
{
  expr::term_manager& tm = F->get_state_type()->tm();
  d_m = new expr::model(tm, false);

  for (unsigned i = 0; i< vars_to_eliminate.size(); ++ i) {
    d_vars_to_eliminate.insert(vars_to_eliminate[i]);
  }

  for (unsigned i = 0; i < variables.size(); ++ i) {
    expr::term_ref x = variables[i];
    expr::value v = d_m->get_term_value(values[i]);
    d_m->set_variable_value(x, v);
    if (d_vars_to_eliminate.count(x)  == 0) {
      d_vars_to_keep.insert(x);
    }
  }
}

void generalize::to_stream(std::ostream& out) const  {
  out << "[" << get_command_type_string() << " " << *d_F << " " << *d_m << "]";
}

void generalize::run(system::context* ctx, engine* e) {

  const system::state_type* state_type = d_F->get_state_type();
  expr::term_manager& tm = state_type->tm();
  smt::solver* solver = smt::factory::mk_default_solver(tm, ctx->get_options(), ctx->get_statistics());
  expr::term_ref F = d_F->get_formula();

  solver->add_variables(d_vars_to_eliminate.begin(), d_vars_to_eliminate.end(), smt::solver::CLASS_B);
  solver->add_variables(d_vars_to_keep.begin(), d_vars_to_keep.end(), smt::solver::CLASS_A);
  solver->add(F, smt::solver::CLASS_T);
  expr::term_ref result = solver->generalize(smt::solver::GENERALIZE_BACKWARD, d_m);

  state_type->use_namespace();
  state_type->use_namespace(system::state_type::STATE_CURRENT);
  std::cout << result << std::endl;
  ctx->tm().pop_namespace();
  ctx->tm().pop_namespace();
}

generalize::~generalize() {
  delete d_F;
}

}
}
