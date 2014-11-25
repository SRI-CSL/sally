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
#include "engine/engine.h"

using namespace std;
using namespace boost::program_options;

using namespace sal2;
using namespace sal2::expr;

/** Parses the program arguments. */
void getOptions(int argc, char* argv[], variables_map& variables);

int main(int argc, char* argv[]) {

  // Get the options from command line and config files
  variables_map options;
  getOptions(argc, argv, options);

  // Get the files to run
  vector<string> files = options.at("input").as< vector<string> >();

  // Set the verbosity
  output::set_verbosity(cout, options.at("verbosity").as<size_t>());
  output::set_verbosity(cerr, options.at("verbosity").as<size_t>());

  // Typecheck by default
  bool type_check = true;

  // Create the term manager
  expr::term_manager tm(type_check);
  cout << expr::set_tm(tm);
  cerr << expr::set_tm(tm);

  // Create the context
  system::context ctx(tm);

  // Add options to the context
  ctx.set_options(options);

  // Create the engine
  engine* engine_to_use = 0;
  if (options.count("engine") > 0) {
    try {
      engine_to_use = engine::mk_engine(options.at("engine").as<string>(), ctx);
    } catch (const sal2::exception& e) {
      cerr << e << endl;
      exit(1);
    }
  }

  // Go through all the files and run them
  for (size_t i = 0; i < files.size(); ++ i) {

    try {
      if (output::get_verbosity(cout) > 0) {
        cout << "Processing " << files[i] << endl;
      }

      // Create the parser
      parser::parser mcmt_parser(ctx, files[i].c_str());

      // Parse an process each command
      for (parser::command* cmd = mcmt_parser.parse_command(); cmd != 0; delete cmd, cmd = mcmt_parser.parse_command()) {

        if (output::get_verbosity(cout) > 0) {
          cout << "Got command " << *cmd << endl;
        }

        // If only parsing, just ignore the command
        if (options.count("parse-only") > 0) {
          continue;
        }

        // Run the command
        if (engine_to_use) {
          cmd->run(engine_to_use);
        }
      }

    } catch (sal2::exception& e) {
      cerr << e << std::endl;
      exit(1);
    }
  }

  // Delete the engine
  if (engine_to_use != 0) {
    delete engine_to_use;
  }
}

std::string get_engines_list() {
  std::vector<string> engines;
  engine::get_engines(engines);
  std::stringstream out;
  out << "The engine to use: ";
  for (size_t i = 0; i < engines.size(); ++ i) {
    if (i) { out << ", "; }
    out << engines[i];
  }
  return out.str();
}

void getOptions(int argc, char* argv[], variables_map& variables)
{
  // Define the main options
  options_description description("General options");
  description.add_options()
      ("help,h", "Prints this help message.")
      ("verbosity,v", value<size_t>()->default_value(0), "Set the verbosity of the output.")
      ("input,i", value<vector<string> >()->required(), "A problem to solve.")
      ("parse-only", "Just parse, don't solve.")
      ("engine", value<string>(), get_engines_list().c_str())
      ;

  // Get the individual engine options
  engine::setup_options(description);

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
