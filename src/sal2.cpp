/*
 * sal2.cpp
 *
 *  Created on: Oct 2, 2014
 *      Author: dejan
 */

#include <iostream>
#include <boost/program_options.hpp>

#include "expr/term.h"
#include "parser/parser.h"
#include "utils/output.h"

using namespace std;
using namespace boost::program_options;

using namespace sal2;
using namespace sal2::expr;

/* Parses the program arguments. */
void getOptions(int argc, char* argv[], variables_map& variables);

int main(int argc, char* argv[]) {

  // Get the options from command line and config files
  variables_map options;
  getOptions(argc, argv, options);

  // Get the files to run
  vector<string> files;
  if (options.count("input") > 0) {
    // We have filenames
    files = options.at("input").as< vector<string> >();
  } else {
    // Otherwise read from standard input
    files.push_back("-");
  }

  // Set the verbosity
  output::set_verbosity(cout, options.at("verbosity").as<size_t>());

  // Typecheck by default
  bool type_check = true;

  // Go through all the files and run them
  for (size_t i = 0; i < files.size(); ++ i) {

    if (output::get_verbosity(cout) > 0) {
      cout << "Processing " << files[i] << endl;
    }

    // Create the term manager
    expr::term_manager tm(type_check);

    // Create the parser
    parser::parser mcmt_parser(tm, files[i].c_str());

    // Parse an process
    mcmt_parser.parse_command();
  }
}

void getOptions(int argc, char* argv[], variables_map& variables)
{
  // Define the options
  options_description description("Options");
  description.add_options()
      ("help,h", "Prints this help message")
      ("verbosity,v", value<size_t>()->default_value(0), "Set the verbosity of the output.")
      ("input,i", value<vector<string> >(), "A problem to solve")
      ;

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
  if (parseError || variables.count("help") > 0) {
    if (parseError) {
      cout << "Error parsing command line!" << endl;
    }
    cout << description << endl;
    if (parseError) {
      exit(1);
    } else {
      exit(0);
    }
  }
}
