/*
 * parser.h
 *
 *  Created on: Nov 4, 2014
 *      Author: dejan
 */

#pragma once

#include <sstream>

#include "utils/exception.h"
#include "parser/command.h"

namespace sal2 {

namespace expr {
class term_manager;
}

namespace parser {

class parser_exception : public exception {
public:
  parser_exception(std::string msg)
  : exception(msg) {}

  parser_exception(std::string msg, std::string filename, int line, int pos)
  {
    std::stringstream ss;
    ss << filename << ":" << line << ":" << pos << ": " << msg;
    d_msg = ss.str();
  }

};

class parser_internal;

class parser {

  parser_internal* d_internal;

public:

  parser(expr::term_manager& tm, const char* filename);
  ~parser();

  /** Parse the next command from the input */
  command* parse_command();
};

}
}
