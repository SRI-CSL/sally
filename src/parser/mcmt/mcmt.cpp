/*
 * mcmt.cpp
 *
 *  Created on: Dec 10, 2014
 *      Author: dejan
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



