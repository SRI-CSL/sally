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

#include <iostream>
#include <fstream>
#include <boost/program_options.hpp>
#include <boost/thread.hpp>

#include "command/command.h"
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

/** Parses the program arguments. */
void parse_options(int argc, char* argv[], variables_map& variables, utils::statistics& stats);

/** Prints statistics to the given output and given time slice */
void live_stats(const utils::statistics* stats, std::string file, unsigned time);

int main(int argc, char* argv[]) {

  try {

    // Get the options from command line and config files
    variables_map boost_opts;
    utils::statistics stats;
    parse_options(argc, argv, boost_opts, stats);
    options opts(boost_opts);

    // Get the files to run
    vector<string>& files = boost_opts.at("input").as<vector<string> >();

    // Set the verbosity
    output::set_verbosity(cout, opts.get_unsigned("verbosity"));
    output::set_verbosity(cerr, opts.get_unsigned("verbosity"));

    // Set the output language
    output::language out_lang = output::language_from_string(opts.get_string("output-language"));
    output::set_output_language(cout, out_lang);
    output::set_output_language(cerr, out_lang);

    // Set whether to use lets in printouts
    bool use_lets = boost_opts.count("no-lets") == 0;
    output::set_use_lets(cout, use_lets);
    output::set_use_lets(cerr, use_lets);

    // Set any trace tags if passed in
    if (boost_opts.count("debug") > 0) {
      vector<string>& tags = boost_opts.at("debug").as<vector<string> >();
      for (size_t i = 0; i < tags.size(); ++i) {
        output::trace_tag_enable(tags[i]);
      }
    }

    // Create the statistics
    utils::stat_string* stat_filename = static_cast<utils::stat_string*>(stats.register_stat("filename"));
    utils::stat_string* stat_engine = static_cast<utils::stat_string*>(stats.register_stat("engine"));
    utils::stat_string* stat_solver = static_cast<utils::stat_string*>(stats.register_stat("solver"));
    utils::stat_timer* stat_time = static_cast<utils::stat_timer*>(stats.register_stat("time"));
    utils::stat_string* stat_result = static_cast<utils::stat_string*>(stats.register_stat("result"));
    stat_filename->set_value(files[0]);
    stat_engine->set_value(opts.has_option("engine") ? opts.get_string("engine") : "none");
    stat_solver->set_value(opts.get_string("solver"));
    stat_result->set_value("unknown");
    stat_time->start();

    // Create the term manager
    expr::term_manager tm(stats);
    cout << expr::set_tm(tm);
    cerr << expr::set_tm(tm);

    // Create the context
    system::context ctx(tm, opts, stats);

    // Set the default solver for the solver factory
    smt::factory::set_default_solver(opts.get_string("solver"));

    // Enable smt2 output if enabled
    if (opts.has_option("smt2-output")) {
      smt::factory::enable_smt2_output(opts.get_string("smt2-output"));
    }

    // Create the engine
    engine* engine_to_use = 0;
    if (opts.has_option("engine")) {
      engine_to_use = engine_factory::mk_engine(boost_opts.at("engine").as<string>(), ctx);
    }

    // Setup live stats if asked
    boost::thread *stats_worker = 0;
    if (opts.has_option("live-stats")) {
      std::string stats_out = opts.get_string("live-stats");
      unsigned time = boost_opts.at("live-stats-time").as<unsigned>();
      stats_worker = new boost::thread(live_stats, &stats, stats_out, time);
    }

    // Go through all the files and run them
    for (size_t i = 0; i < files.size(); ++i) {

      MSG(1) << "Processing " << files[i] << endl;

      // Create the parser
      parser::input_language language = parser::parser::guess_language(files[i]);
      parser::parser p(ctx, language, files[i].c_str());

      // Parse an process each command
      for (cmd::command* cmd = p.parse_command(); cmd != 0; delete cmd, cmd = p.parse_command()) {

        MSG(2) << "Got command " << *cmd << endl;
        // Run the command
        cmd->run(&ctx, engine_to_use);

        if (boost_opts.count("stats") > 0) {
          std::cout << "Stats after " << cmd->get_command_type_string() << std::endl;
          stats.to_stream(" - ", std::cout);
        } 

        if (cmd->get_type() == cmd::QUERY && boost_opts.count("stats-format") > 0) {
          stat_result->set_value(engine_to_use->get_last_result_string());
          std::string format = boost_opts.at("stats-format").as<string>();
          std::cout << stats.format(format) << std::endl;
        }
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
  } catch (const char* s) {
    cerr << s << endl;
    exit(1);
  } catch (...) {
    cerr << "Unexpected error!" << endl;
    exit(1);
  }
}

std::string get_engines_list() {
  std::vector<string> engines;
  engine_factory::get_engines(engines);
  std::stringstream out;
  out << "The engine to use: ";
  for (size_t i = 0; i < engines.size(); ++ i) {
    if (i) { out << ", "; }
    out << engines[i];
  }
  return out.str();
}

std::string get_solver_list() {
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

void parse_options(int argc, char* argv[], variables_map& variables, utils::statistics& stats)
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
      ("show-invariant", "Show the invariant if property is proved.")
      ("parse-only", "Just parse, don't solve.")
      ("engine", value<string>(), get_engines_list().c_str())
      ("solver", value<string>()->default_value(smt::factory::get_default_solver_id()), get_solver_list().c_str())
      ("solver-logic", value<string>(), "Optional smt2 logic to set to the solver (e.g. QF_LRA, QF_LIA, ...).")
      ("output-language", value<string>()->default_value("mcmt"), get_output_languages_list().c_str())
      ("lsal-extensions", "Use lsal extensions to the MCMT language")
      ("no-input-namespace", "Don't use input namespace in the the MCMT language")
      ("stats", "Show statistics after every command")
      ("stats-format", value<string>(), "Show statistics in the given format after every query. See --stats-help for more information.")
      ("stats-help", "Show help for statistics formatting.")
      ("live-stats", value<string>(), "Output live statistic to the given file (- for stdout).")
      ("live-stats-time", value<unsigned>()->default_value(100), "Time period for statistics output (in miliseconds)")
      ("smt2-output", value<string>(), "Generate smt2 logs of solver queries with given prefix.")
      ("no-lets", "Don't use let expressions in printouts.");
      ;

  // Get the individual engine options
  engine_factory::setup_options(description);

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

  if (variables.count("stats-help") > 0) {
    cout << stats.get_help_string() << endl;
    exit(0);
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

void live_stats(const utils::statistics* stats, std::string file, unsigned time) {

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
      boost::this_thread::sleep(boost::posix_time::milliseconds(time));
      *out << *stats << endl;
    }
  } catch (boost::thread_interrupted&) {}

  if (of_out) {
    delete of_out;
  }
}
