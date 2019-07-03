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

#include "parser/smt2/smt2.h"

#include "parser/smt2/smt2_state.h"
#include "parser/smt2/smt2Lexer.h"
#include "parser/smt2/smt2Parser.h"

namespace sally {
namespace parser {

template<>
struct antlr_parser_traits<INPUT_SMT2> {

  typedef psmt2Lexer pLangLexer;
  typedef psmt2Parser pLangParser;

  typedef smt2_state langState;

  static
  psmt2Lexer newLexer(pANTLR3_INPUT_STREAM instream) {
    return smt2LexerNew(instream);
  }

  static
  psmt2Parser newParser(pANTLR3_COMMON_TOKEN_STREAM instream) {
    return smt2ParserNew(instream);
  }
};

internal_parser_interface* new_smt2_parser(const system::context& ctx, const char* filename) {
  return new antlr_parser<INPUT_SMT2>(ctx, filename);
}


}
}



