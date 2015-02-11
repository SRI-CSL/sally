/*
 * sally.cpp
 *
 *  Created on: Oct 2, 2014
 *      Author: dejan
 */

#include <iostream>
#include <fstream>
#include <boost/program_options.hpp>
#include <boost/thread.hpp>

#include "expr/term_manager.h"
#include "utils/output.h"
#include "system/context.h"
#include "parser/parser.h"
#include "engine/factory.h"
#include "smt/factory.h"
#include "utils/trace.h"
#include "utils/statistics.h"

using namespace std;
using namespace boost::program_options;

using namespace sally;
using namespace sally::expr;

/** Parses the program arguments. */
void parse_options(int argc, char* argv[], variables_map& variables);

/** Prints statistics to the given output */
void live_stats(const utils::statistics* stats, std::string file);

int main(int argc, char* argv[]) {

  try {

    // Get the options from command line and config files
    variables_map boost_opts;
    parse_options(argc, argv, boost_opts);
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

    // Create the statistics */
    utils::statistics stats;
    stats.add(new utils::stat_timer("sally::time", true));

    // Create the context
    system::context ctx(tm, opts, stats);

    // Set the default solver for the solver factory
    smt::factory::set_default_solver(opts.get_string("solver"));

    // Create the engine
    engine* engine_to_use = 0;
    if (opts.has_option("engine") > 0) {
      engine_to_use = factory::mk_engine(boost_opts.at("engine").as<string>(), ctx);
    }

    // Setup live stats if asked
    boost::thread *stats_worker = 0;
    if (opts.has_option("live-stats")) {
      std::string stats_out = opts.get_string("live-stats");
      stats_worker = new boost::thread(live_stats, &stats, stats_out);
    }

    // Go through all the files and run them
    for (size_t i = 0; i < files.size(); ++i) {

      MSG(1) << "Processing " << files[i] << endl;

      // Create the parser
      parser::input_language language = parser::parser::guess_language(files[i]);
      parser::parser p(ctx, language, files[i].c_str());

      // Parse an process each command
      for (parser::command* cmd = p.parse_command(); cmd != 0; delete cmd, cmd = p.parse_command()) {

        MSG(2) << "Got command " << *cmd << endl;
        // Run the command
        cmd->run(&ctx, engine_to_use);
      }
    }

    // Delete the engine
    if (engine_to_use != 0) {
      delete engine_to_use;
    }

    // Stop the live stats thread
    if (stats_worker) {
      stats_worker->interrupt();
      stats_worker->join();
    }
  } catch (sally::exception& e) {
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

void parse_options(int argc, char* argv[], variables_map& variables)
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
      ("arith-eq-to-ineq", "Rewrite equalities into inqualities.")
      ("lsal-extensions", "Use lsal extensions to the MCMT language")
      ("live-stats", value<string>(), "Output live statistic to the given file.")
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

void live_stats(const utils::statistics* stats, std::string file) {

  ostream* out = 0;
  ofstream* of_out = 0;

  if (file == "-") {
    out = &cout;
  } else {
    out = of_out = new ofstream(file.c_str());
  }

  // Output headers
  stats->headers_to_stream(*out);
  *out << std::endl;

  try {
    // Output stats
    for (;;) {
      boost::this_thread::sleep(boost::posix_time::milliseconds(100));
      *out << *stats << endl;
    }
  } catch (boost::thread_interrupted&) {}

  if (of_out) {
    delete of_out;
  }
}
