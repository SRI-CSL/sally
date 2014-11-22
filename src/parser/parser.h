/*
 * parser.h
 *
 *  Created on: Nov 4, 2014
 *      Author: dejan
 */

#pragma once

#include "utils/exception.h"
#include "parser/command.h"

namespace sal2 {

namespace system {
  class context;
}

namespace parser {

class parser_exception : public exception {

  /** Filename */
  std::string d_filename;

  /** Line of the error */
  int d_line;

  /** Position of the error */
  int d_pos;


public:

  parser_exception(std::string msg)
  : exception(msg)
  , d_filename("")
  , d_line(-1)
  , d_pos(-1)
  {}

  parser_exception(std::string msg, std::string filename, int line, int pos)
  : exception(msg)
  , d_filename(filename)
  , d_line(line)
  , d_pos(pos)
  {}

  bool has_line_info() const {
    return d_line != -1;
  }

  int get_line() const {
    return d_line;
  }

  int get_position() const {
    return d_pos;
  }

  std::string get_filename() const {
    return d_filename;
  }

  void to_stream(std::ostream& out) const;
};

class parser_internal;

class parser {

  parser_internal* d_internal;

public:

  parser(system::context& ctx, const char* filename);
  ~parser();

  /** Parse the next command from the input */
  command* parse_command();
};

}
}
