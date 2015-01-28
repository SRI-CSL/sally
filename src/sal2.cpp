/*
 * sal2.cpp
 *
 *  Created on: Oct 2, 2014
 *      Author: dejan
 */

#include <iostream>
#include <boost/program_options.hpp>

#include "expr/term_manager.h"
#include "utils/output.h"
#include "system/context.h"
#include "parser/parser.h"
#include "engine/factory.h"
#include "smt/factory.h"

using namespace std;
using namespace boost::program_options;

using namespace sal2;
using namespace sal2::expr;

/** Parses the program arguments. */
void parseOptions(int argc, char* argv[], variables_map& variables);

int main(int argc, char* argv[]) {

  try {

    // Get the options from command line and config files
    variables_map boost_opts;
    parseOptions(argc, argv, boost_opts);
    options opts(boost_opts);

    // Get the files to run
    vector<string>& files = boost_opts.at("input").as<vector<string> >();

    // Set the verbosity
    output::set_verbosity(cout, opts.get_unsigned("verbosity"));
    output::set_verbosity(cerr, opts.get_unsigned("verbosity"));

    // Set the output language
    output::language out_lang = output::language_from_string(
        opts.get_string("output-language"));
    output::set_output_language(cout, out_lang);
    output::set_output_language(cerr, out_lang);

    // Set any trace tags if passed in
    if (boost_opts.count("debug") > 0) {
      vector<string>& tags = boost_opts.at("debug").as<vector<string> >();
      for (size_t i = 0; i < tags.size(); ++i) {
        output::trace_tag_enable(tags[i]);
      }
    }

    // Create the term manager
    expr::term_manager tm(true);
    cout << expr::set_tm(tm);
    cerr << expr::set_tm(tm);

    // Rewrite inequalities if asked to
    tm.set_eq_rewrite(opts.get_bool("arith-eq-to-ineq"));

    // Create the context
    system::context ctx(tm, opts);

    // Set the default solver for the solver factory
    smt::factory::set_default_solver(opts.get_string("solver"));

    // Create the engine
    engine* engine_to_use = 0;
    if (opts.has_option("engine") > 0) {
      engine_to_use = factory::mk_engine(boost_opts.at("engine").as<string>(), ctx);
    }

    // Go through all the files and run them
    for (size_t i = 0; i < files.size(); ++i) {
      if (output::get_verbosity(cout) > 0) {
        cout << "Processing " << files[i] << endl;
      }

      // Create the parser
      parser::input_language language = parser::parser::guess_language(files[i]);
      parser::parser mcmt_parser(ctx, language, files[i].c_str());

      // Parse an process each command
      for (parser::command* cmd = mcmt_parser.parse_command(); cmd != 0; delete cmd, cmd = mcmt_parser.parse_command()) {
        if (output::get_verbosity(cout) > 2) {
          cout << "Got command " << *cmd << endl;
        }
        // Run the command
        cmd->run(&ctx, engine_to_use);
      }
    }

    // Delete the engine
    if (engine_to_use != 0) {
      delete engine_to_use;
    }
  } catch (sal2::exception& e) {
    cerr << e << endl;
    exit(1);
  } catch (...) {
    cerr << "Unexpected error!" << endl;
    exit(1);
  }
}

std::string get_engines_list() {
  std::vector<string> engines;
  factory::get_engines(engines);
  std::stringstream out;
  out << "The engine to use: ";
  for (size_t i = 0; i < engines.size(); ++ i) {
    if (i) { out << ", "; }
    out << engines[i];
  }
  return out.str();
}

std::string get_solvers_list() {
  std::vector<string> solvers;
  smt::factory::get_solvers(solvers);
  std::stringstream out;
  out << "The SMT solver to use: ";
  for (size_t i = 0; i < solvers.size(); ++ i) {
    if (i) { out << ", "; }
    out << solvers[i];
  }
  return out.str();
}

std::string get_output_languages_list() {
  std::stringstream out;
  out << "Output language to use: ";
  for (int i = 0; i < output::UNKNOWN; ++ i) {
    if (i) { out << ", "; }
    out << output::language_to_string(output::language(i));
  }
  return out.str();
}

void parseOptions(int argc, char* argv[], variables_map& variables)
{
  // Define the main options
  options_description description("General options");
  description.add_options()
      ("help,h", "Prints this help message.")
      ("verbosity,v", value<unsigned>()->default_value(0), "Set the verbosity of the output.")
      ("input,i", value<vector<string> >()->required(), "A problem to solve.")
#ifndef NDEBUG
      ("debug,d", value<vector<string> >(), "Any tags to trace (only for debug builds).")
#endif
      ("show-trace", "Show the counterexample trace if found.")
      ("parse-only", "Just parse, don't solve.")
      ("engine", value<string>(), get_engines_list().c_str())
      ("solver", value<string>()->default_value(smt::factory::get_default_solver_id()), get_solvers_list().c_str())
      ("output-language", value<string>()->default_value("mcmt"), get_output_languages_list().c_str())
      ("arith-eq-to-ineq", value<bool>()->default_value(false), "Rewrite equalities into inqualities.")
      ;

  // Get the individual engine options
  factory::setup_options(description);

  // Get the individual solver options
  smt::factory::setup_options(description);

  // The input files can be positional
  positional_options_description positional;
  positional.add("input", -1);

  // Parse the options
  bool parseError = false;
  try {
    store(command_line_parser(argc, argv).options(description).positional(positional).run(), variables);
  } catch (...) {
    parseError = true;
  }

  // If help needed, print it out
  if (parseError || variables.count("help") > 0 || variables.count("input") == 0) {
    if (parseError) {
      cout << "Error parsing command line!" << endl;
    }
    cout << "Usage: " << argv[0] << " [options] input ..." << endl;
    cout << description << endl;
    if (parseError) {
      exit(1);
    } else {
      exit(0);
    }
  }
}
