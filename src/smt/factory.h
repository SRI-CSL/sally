/*
 * factory.h
 *
 *  Created on: Nov 26, 2014
 *      Author: dejan
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
