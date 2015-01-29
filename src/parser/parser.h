/*
 * parser.h
 *
 *  Created on: Nov 4, 2014
 *      Author: dejan
 */

#pragma once

#include "utils/exception.h"
#include "parser/command.h"

namespace sally {

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

  /** Create an exceptoin with no line information */
  parser_exception(std::string msg);

  /** Create an exception with line information */
  parser_exception(std::string msg, std::string filename, int line, int pos);

  /** Returns true if the exception carries line information */
  bool has_line_info() const;

  /** Get the line number */
  int get_line() const;

  /** Get the position in line */
  int get_position() const;

  /** Get the file name */
  std::string get_filename() const;

  /** Output to stream */
  void to_stream(std::ostream& out) const;
};

class antlr_parser_interface;

enum input_language {
  INPUT_MCMT,
  INPUT_BTOR,
  INPUT_SAL
};

/**
 * Parser for model-checking problems.
 */
class parser {

  /** Internal parser data. */
  antlr_parser_interface* d_internal;

public:

  /** Create a parser for the given language */
  parser(const system::context& ctx, input_language lang, const char* filename);

  /** Destroy the parser */
  ~parser();

  /** Parse the next command from the input */
  command* parse_command();

  /**
   * Returns the language based on the extension of the filename (e.g. given "btor" it
   * returns INPUT_BTOR. By default, it returns INPUT_MCMT.
   */
  static
  input_language guess_language(std::string filename);
};

}
}
