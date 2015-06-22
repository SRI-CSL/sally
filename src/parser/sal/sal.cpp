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

#include "parser/sal/sal.h"
#include "parser/sal/sal_state.h"

#include "parser/sal/salLexer.h"
#include "parser/sal/salParser.h"

namespace sally {
namespace parser {

template<>
struct antlr_parser_traits<INPUT_SAL> {

  typedef psalLexer pLangLexer;
  typedef psalParser pLangParser;

  typedef sal_state langState;

  static
  psalLexer newLexer(pANTLR3_INPUT_STREAM instream) {
    return salLexerNew(instream);
  }

  static
  psalParser newParser(pANTLR3_COMMON_TOKEN_STREAM instream) {
    return salParserNew(instream);
  }
};

antlr_parser_interface* new_sal_parser(const system::context& ctx, const char* filename) {
  return new antlr_parser<INPUT_SAL>(ctx, filename);
}

}
}


