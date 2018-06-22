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

#include "parser/parser.h"
#include "parser/antlr_parser.h"

#include "parser/mcmt/mcmt.h"
#include "parser/chc/chc.h"
#include "parser/btor/btor.h"
#include "parser/sal/sal.h"
#include "parser/aiger/aiger.h"

#include <iostream>

namespace sally {
namespace parser {

parser_exception::parser_exception(expr::term_manager* tm)
: exception(tm)
, d_filename("")
, d_line(-1)
, d_pos(-1)
{}

parser_exception::parser_exception(expr::term_manager& tm)
: exception(tm)
, d_filename("")
, d_line(-1)
, d_pos(-1)
{}

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
  case INPUT_AIGER:
    d_internal = new_aiger_parser(ctx, filename);
    break;
  case INPUT_CHC:
    d_internal = new_chc_parser(ctx, filename);
    break;
  default:
    assert(false);
  }
}

parser::~parser() {
  delete d_internal;
}

cmd::command* parser::parse_command() {
  try {
    return d_internal->parse_command();
  } catch (const parser_exception& e) {
    if (!e.has_line_info()) {
      // Add line information
      throw parser_exception(e.get_message(), d_internal->get_filename(), d_internal->get_current_parser_line(), d_internal->get_current_parser_position());
    } else {
      throw e;
    }
  } catch (const sally::exception& e) {
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
    if (extension == "aig") {
      return INPUT_AIGER;
    }
    if (extension == "smt2") {
      return INPUT_CHC;
    }
    return INPUT_MCMT;
  }
}

}
}
