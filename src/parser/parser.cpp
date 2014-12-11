/*
 * parser.cpp
 *
 *  Created on: Nov 4, 2014
 *      Author: dejan
 */

#include "parser/parser.h"
#include "parser/antlr_parser.h"

#include "parser/mcmt/mcmt.h"
#include "parser/btor/btor.h"
#include "parser/sal/sal.h"

#include <iostream>

namespace sal2 {
namespace parser {

parser_exception::parser_exception(std::string msg)
: exception(msg)
, d_filename("")
, d_line(-1)
, d_pos(-1)
{}

parser_exception::parser_exception(std::string msg, std::string filename, int line, int pos)
: exception(msg)
, d_filename(filename)
, d_line(line)
, d_pos(pos)
{}

bool parser_exception::has_line_info() const {
  return d_line != -1;
}

int parser_exception::get_line() const {
  return d_line;
}

int parser_exception::get_position() const {
  return d_pos;
}

std::string parser_exception::get_filename() const {
  return d_filename;
}

void parser_exception::to_stream(std::ostream& out) const {
  out << "Parse error: ";
  if (d_line != -1) {
    out << get_filename() << ":" << get_line() << ":" << get_position() << ": ";
  }
  out << get_message();
}

parser::parser(const system::context& ctx, input_language lang, const char* filename)
{
  switch (lang) {
  case INPUT_MCMT:
    d_internal = new_mcmt_parser(ctx, filename);
    break;
  case INPUT_BTOR:
    d_internal = new_btor_parser(ctx, filename);
    break;
  case INPUT_SAL:
    d_internal = new_sal_parser(ctx, filename);
    break;
  default:
    assert(false);
  }
}

parser::~parser() {
  delete d_internal;
}

command* parser::parse_command() {
  try {
    return d_internal->parse_command();
  } catch (const parser_exception& e) {
    if (!e.has_line_info()) {
      // Add line information
      throw parser_exception(e.get_message(), d_internal->get_filename(), d_internal->get_current_parser_line(), d_internal->get_current_parser_position());
    } else {
      throw e;
    }
  } catch (const sal2::exception& e) {
    throw parser_exception(e.get_message(), d_internal->get_filename(), d_internal->get_current_parser_line(), d_internal->get_current_parser_position());
  }
}

input_language parser::guess_language(std::string filename) {
  std::string::size_type index = filename.find_last_of('.');
  if (index == filename.npos) {
    // No extension
    return INPUT_MCMT;
  } else {
    std::string extension = filename.substr(index + 1);
    if (extension == "btor") {
      return INPUT_BTOR;
    }
    if (extension == "sal") {
      return INPUT_SAL;
    }
    return INPUT_MCMT;
  }
}

}
}
