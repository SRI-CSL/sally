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
