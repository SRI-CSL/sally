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

#include "chc.h"

#include "chc_state.h"
#include "chcLexer.h"
#include "chcParser.h"

namespace sally {
namespace parser {

template<>
struct antlr_parser_traits<INPUT_CHC> {

  typedef pchcLexer pLangLexer;
  typedef pchcParser pLangParser;

  typedef chc_state langState;

  static
  pchcLexer newLexer(pANTLR3_INPUT_STREAM instream) {
    return chcLexerNew(instream);
  }

  static
  pchcParser newParser(pANTLR3_COMMON_TOKEN_STREAM instream) {
    return chcParserNew(instream);
  }
};

internal_parser_interface* new_chc_parser(const system::context& ctx, const char* filename) {
  return new antlr_parser<INPUT_CHC>(ctx, filename);
}


}
}



