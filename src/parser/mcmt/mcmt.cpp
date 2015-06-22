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

#include "parser/mcmt/mcmt.h"

#include "parser/mcmt/mcmt_state.h"
#include "parser/mcmt/mcmtLexer.h"
#include "parser/mcmt/mcmtParser.h"

namespace sally {
namespace parser {

template<>
struct antlr_parser_traits<INPUT_MCMT> {

  typedef pmcmtLexer pLangLexer;
  typedef pmcmtParser pLangParser;

  typedef mcmt_state langState;

  static
  pmcmtLexer newLexer(pANTLR3_INPUT_STREAM instream) {
    return mcmtLexerNew(instream);
  }

  static
  pmcmtParser newParser(pANTLR3_COMMON_TOKEN_STREAM instream) {
    return mcmtParserNew(instream);
  }
};

antlr_parser_interface* new_mcmt_parser(const system::context& ctx, const char* filename) {
  return new antlr_parser<INPUT_MCMT>(ctx, filename);
}


}
}



