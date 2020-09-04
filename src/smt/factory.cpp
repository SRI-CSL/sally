/**
 * This file is part of sally.
 * Copyright (C) 2015 SRI International.
 *
 * Sally is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Sally is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with sally.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "smt/factory.h"
#include "utils/module_setup.h"
#include "smt/smt2_output_wrapper.h"

#include <iostream>
#include <iomanip>

namespace sally {
namespace smt {

/** Type for setting up individual engines */
class solver_data : public module_data<solver, solver_context> {
public:
  solver_data();
};

/** Map from id's to engine information */
static solver_data s_solver_data;

std::string factory::s_default_solver;

size_t factory::s_total_instances = 0;

bool factory::s_generate_smt = false;

std::string factory::s_smt2_prefix;

void factory::set_default_solver(std::string id) {
  s_default_solver = id;
}

solver* factory::mk_default_solver(expr::term_manager& tm, const options& opts, utils::statistics& stats) {
  if (s_default_solver.size() == 0) {
    throw exception("No default solver set.");
  }
  return mk_solver(s_default_solver, tm, opts, stats);
}

solver* factory::mk_solver(std::string id, expr::term_manager& tm, const options& opts, utils::statistics& stats) {
  solver_context ctx(tm, opts, stats);
  if (output::get_verbosity(std::cout) > 2) {
    std::cout << "Creating an instance of " + id + " solver." << std::endl;
  }
  solver* solver = s_solver_data.get_module_info(id).new_instance(ctx);
  s_total_instances ++;
  if (s_generate_smt) {
    std::stringstream ss;
    ss << s_smt2_prefix << "." << std::setfill('0') << std::setw(3) << s_total_instances << "." << solver->get_name() << ".smt2";
    solver = new smt2_output_wrapper(tm, opts, stats, solver, ss.str());
  }
  return solver;
}

void factory::setup_options(boost::program_options::options_description& options) {
  for (solver_data::const_iterator it = s_solver_data.data().begin(); it != s_solver_data.data().end(); ++ it) {
    std::stringstream ss;
    ss << "Solver '" << it->second->get_id() << "'." << std::endl;
    ss << it->second->get_description() << std::endl;
    ss << "Options";
    boost::program_options::options_description solver_options(ss.str());
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

void factory::enable_smt2_output(std::string prefix) {
  s_generate_smt = true;
  s_smt2_prefix = prefix;
}

}
}

#include "smt/solvers_list.h"
