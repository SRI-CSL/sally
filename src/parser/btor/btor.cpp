/*
 * btor.cpp
 *
 *  Created on: Dec 10, 2014
 *      Author: dejan
 */

#include "parser/btor/btor.h"
#include "parser/btor/btor_state.h"

#include "parser/btor/btorLexer.h"
#include "parser/btor/btorParser.h"

namespace sally {
namespace parser {

template<>
struct antlr_parser_traits<INPUT_BTOR> {

  typedef pbtorLexer pLangLexer;
  typedef pbtorParser pLangParser;

  typedef btor_state langState;

  static
  pLangLexer newLexer(pANTLR3_INPUT_STREAM instream) {
    return btorLexerNew(instream);
  }

  static
  pLangParser newParser(pANTLR3_COMMON_TOKEN_STREAM instream) {
    return btorParserNew(instream);
  }

};

antlr_parser_interface* new_btor_parser(const system::context& ctx, const char* filename) {
  return new antlr_parser<INPUT_BTOR>(ctx, filename);
}

}
}


