/*
 * factory.cpp
 *
 *  Created on: Nov 26, 2014
 *      Author: dejan
 */

#include "smt/factory.h"
#include "utils/module_setup.h"

namespace sal2 {
namespace smt {

/** Type for setting up individual engines */
class solver_data : public module_data<solver, solver_context> {
public:
  solver_data();
};

/** Map from id's to engine information */
static solver_data s_solver_data;

std::string factory::s_default_solver("yices2");

void factory::set_default_solver(std::string id) {
  s_default_solver = id;
}

solver* factory::mk_default_solver(expr::term_manager& tm, const options& opts) {
  return mk_solver(s_default_solver, tm, opts);
}

solver* factory::mk_solver(std::string id, expr::term_manager& tm, const options& opts) {
  solver_context ctx(tm, opts);
  if (output::get_verbosity(std::cout) > 0) {
    std::cout << "Creating an instance of " + id + " solver." << std::endl;
  }
  return s_solver_data.get_module_info(id).new_instance(ctx);
}

void factory::setup_options(boost::program_options::options_description& options) {
  for (solver_data::const_iterator it = s_solver_data.data().begin(); it != s_solver_data.data().end(); ++ it) {
    boost::program_options::options_description solver_options(it->second->get_id() + " options");
    it->second->setup_options(solver_options);
    if (solver_options.options().size() > 0) {
      options.add(solver_options);
    }
  }
}

void factory::get_solvers(std::vector<std::string>& out) {
  for (solver_data::const_iterator it = s_solver_data.data().begin(); it != s_solver_data.data().end(); ++ it) {
    out.push_back(it->second->get_id());
  }
}

}
}

#include "smt/solvers_list.h"
