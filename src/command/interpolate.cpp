#include "interpolate.h"

#include "smt/factory.h"
#include "system/state_type.h"

#include <iostream>

namespace sally {
namespace cmd {

interpolate::interpolate(system::state_formula* A, system::state_formula* B)
: command(INTERPOLATE)
, d_A(A)
, d_B(B)
{
}

void interpolate::to_stream(std::ostream& out) const  {
  out << "[" << get_command_type_string() << " " << *d_A << " " << *d_B << "]";
}

void interpolate::run(system::context* ctx, engine* e) {

  const system::state_type* state_type = d_A->get_state_type();
  expr::term_manager& tm = state_type->tm();
  smt::solver* solver = smt::factory::mk_default_solver(tm, ctx->get_options(), ctx->get_statistics());

  expr::term_ref A = d_A->get_formula();
  expr::term_ref B = d_B->get_formula();

  solver->add(A, smt::solver::CLASS_A);
  solver->add(B, smt::solver::CLASS_B);

  expr::term_ref result = solver->interpolate();

  state_type->use_namespace();
  state_type->use_namespace(system::state_type::STATE_CURRENT);
  std::cout << result << std::endl;
  ctx->tm().pop_namespace();
  ctx->tm().pop_namespace();
}

interpolate::~interpolate() {
  delete d_A;
  delete d_B;
}

}
}
