/*
 * mcmt_parser_traits.h
 *
 *  Created on: Dec 1, 2014
 *      Author: dejan
 */

#pragma once

#include "parser/btor/btor_state.h"

#include "parser/btor/btorLexer.h"
#include "parser/btor/btorParser.h"

namespace sal2 {
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

}
}
