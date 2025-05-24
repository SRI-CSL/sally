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

#include "parser/btor2/btor2.h"
#include "parser/btor2/btor2_state.h"

#include "parser/btor2/btor2Lexer.h"
#include "parser/btor2/btor2Parser.h"

namespace sally {
namespace parser {

template<>
struct antlr_parser_traits<INPUT_BTOR2> {

  typedef pbtor2Lexer pLangLexer;
  typedef pbtor2Parser pLangParser;

  typedef btor2_state langState;

  static
  pLangLexer newLexer(pANTLR3_INPUT_STREAM instream) {
    return btor2LexerNew(instream);
  }

  static
  pLangParser newParser(pANTLR3_COMMON_TOKEN_STREAM instream) {
    return btor2ParserNew(instream);
  }

};

internal_parser_interface* new_btor2_parser(const system::context& ctx, const char* filename) {
  return new antlr_parser<INPUT_BTOR2>(ctx, filename);
}

}
}


