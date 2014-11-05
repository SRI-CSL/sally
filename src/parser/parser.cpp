/*
 * parser.cpp
 *
 *  Created on: Nov 4, 2014
 *      Author: dejan
 */

#include "parser/parser.h"
#include "parser/mcmtLexer.h"
#include "parser/mcmtParser.h"

namespace sal2 {
namespace parser {

class parser_internal {

  /** The input */
  pANTLR3_INPUT_STREAM d_input;

  /** The lexer */
  pmcmtLexer d_lexer;

  /** The token stream */
  pANTLR3_COMMON_TOKEN_STREAM d_token_stream;

  /** The parser */
  pmcmtParser d_parser;

public:

  parser_internal(const char* file_to_parse) {
    // Create the input stream for the file
    d_input = antlr3FileStreamNew((pANTLR3_UINT8) file_to_parse, ANTLR3_ENC_8BIT);

    // Create a lexer
    d_lexer = mcmtLexerNew(d_input);

    // Create the token stream
    d_token_stream = antlr3CommonTokenStreamSourceNew(ANTLR3_SIZE_HINT, TOKENSOURCE(d_lexer));

    // Create the parser
    d_parser = mcmtParserNew(d_token_stream);
  }

  ~parser_internal() {
    // TODO: How do I dellocate these bastards
  }

  command* parse_command() {
    return d_parser->command(d_parser);
  }

};

parser::parser(const char* filename)
: d_internal(new parser_internal(filename))
{
}

parser::~parser() {
  delete d_internal;
}

command* parser::parse_command() {
  return d_internal->parse_command();
}

}
}
