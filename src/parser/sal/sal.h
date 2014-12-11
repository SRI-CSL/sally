/*
 * sal_parser_traits.h
 *
 *  Created on: Dec 1, 2014
 *      Author: dejan
 */

#pragma once

#include "parser/sal/sal_state.h"

#include "parser/sal/salLexer.h"
#include "parser/sal/salParser.h"

namespace sal2 {
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

}
}
