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

#pragma once

#include "smt/solver.h"

namespace boost { namespace program_options {
  class options_description;
} }

namespace sally {
namespace smt {

/**
 * Factory for creating SMT solvers.
 */
class factory {

  /** The default solver */
  static std::string s_default_solver;

  /** Number of instances created */
  static size_t s_total_instances;

  /** Wrap solvers to generate smt2 files */
  static bool s_generate_smt;

  /** Prefix of smt2 files */
  static std::string s_smt2_prefix;

public:

  static
  void set_default_solver(std::string id);

  static
  std::string get_default_solver_id();

  static
  solver* mk_default_solver(expr::term_manager& tm, const options& opts);

  static
  solver* mk_solver(std::string id, expr::term_manager& tm, const options& opts);

  static
  void setup_options(boost::program_options::options_description& options);

  static
  void get_solvers(std::vector<std::string>& out);

  static
  void enable_smt2_output(std::string prefix);

};

}
}
