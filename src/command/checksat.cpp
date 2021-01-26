#include "checksat.h"

#include "smt/factory.h"
#include "system/state_type.h"

#include <iostream>

namespace sally {
namespace cmd {

checksat::checksat(system::state_formula* F)
: command(CHECKSAT)
, d_F(F)
{
}

void checksat::to_stream(std::ostream& out) const  {
  out << "[" << get_command_type_string() << " " << *d_F << "]";
}

void checksat::run(system::context* ctx, engine* e) {

  const system::state_type* state_type = d_F->get_state_type();
  expr::term_manager& tm = state_type->tm();
  smt::solver* solver = smt::factory::mk_default_solver(tm, ctx->get_options(), ctx->get_statistics());

  expr::term_ref F = d_F->get_formula();

  solver->add(F, smt::solver::CLASS_A);
  smt::solver::result result = solver->check();

  std::cout << result << std::endl;
}

checksat::~checksat() {
  delete d_F;
}

}
}
