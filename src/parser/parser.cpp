/*
 * parser.cpp
 *
 *  Created on: Nov 4, 2014
 *      Author: dejan
 */

#include "parser/parser.h"
#include "parser/mcmtLexer.h"
#include "parser/mcmtParser.h"
#include "parser/parser_state.h"

namespace sal2 {
namespace parser {

static void sal2_parser_reportError(pANTLR3_BASE_RECOGNIZER recognizer);
static void sal2_lexer_reportError(pANTLR3_BASE_RECOGNIZER recognizer);

class parser_internal {

  /** The input */
  pANTLR3_INPUT_STREAM d_input;

  /** The lexer */
  pmcmtLexer d_lexer;

  /** The token stream */
  pANTLR3_COMMON_TOKEN_STREAM d_token_stream;

  /** The parser */
  pmcmtParser d_parser;

  /** The state of the solver */
  parser_state d_state;

public:

  parser_internal(expr::term_manager& tm, const char* file_to_parse)
  : d_state(tm)
  {
    // Create the input stream for the file
    d_input = antlr3FileStreamNew((pANTLR3_UINT8) file_to_parse, ANTLR3_ENC_8BIT);
    if (d_input == 0) {
      throw parser_exception(std::string("can't open") + file_to_parse);
    }

    // Create a lexer
    d_lexer = mcmtLexerNew(d_input);
    if (d_lexer == 0) {
      throw parser_exception("can't create the lexer");
    }

    // Report the error
    d_lexer->pLexer->rec->reportError = sal2_lexer_reportError;

    // Create the token stream
    d_token_stream = antlr3CommonTokenStreamSourceNew(ANTLR3_SIZE_HINT, TOKENSOURCE(d_lexer));
    if (d_token_stream == 0) {
      throw parser_exception("can't create the token stream");
    }

    // Create the parser
    d_parser = mcmtParserNew(d_token_stream);
    if (d_parser == 0) {
      throw parser_exception("can't create the parser");
    }

    // Mark the internals in the super fields
    d_parser->pParser->super = this;
    d_lexer->pLexer->super = this;

    // Mark the state
    d_parser->pState = &d_state;

    // Add error reporting
    d_parser->pParser->rec->reportError = sal2_parser_reportError;
  }

  ~parser_internal() {
    d_parser->free(d_parser);
    d_token_stream->free(d_token_stream);
    d_lexer->free(d_lexer);
  }

  command* parse_command() {
    return d_parser->command(d_parser);
  }

  /** Returns true if the parser is in error state */
  bool parser_in_error() const {
    return d_parser->pParser->rec->state->error == ANTLR3_TRUE;
  }

  /** Returns the name of the file being parser */
  std::string get_filename() const {
    return (const char*) d_lexer->pLexer->rec->state->tokSource->fileName->chars;
  }

  /** Returns the current line being parsed */
  int get_current_line() const {
    return d_lexer->pLexer->getLine(d_lexer->pLexer);
  }

  /** Returns the position in the curent line that is being parsed */
  int get_current_position() const {
    return d_lexer->pLexer->getCharPositionInLine(d_lexer->pLexer);
  }

  /** Get the parser from the ANTLR parser recognizer */
  static
  parser_internal* from_parser_rec(pANTLR3_BASE_RECOGNIZER recognizer) {
    // Get the ANTLR parser
    pANTLR3_PARSER antlr_parser = (pANTLR3_PARSER) recognizer->super;
    // Return the parser (stored in super)
    return (parser_internal*) antlr_parser->super;
  }

  /** Get the parser form the ANRLT lexer recognizer */
  static
  parser_internal* from_lexer_rec(pANTLR3_BASE_RECOGNIZER recognizer) {
    // Get the ANTLR lexer
    pANTLR3_LEXER lexer = (pANTLR3_LEXER) recognizer->super;
    // Return the parser (stored in super)
    return (parser_internal*) lexer->super;
  }

};

parser::parser(expr::term_manager& tm, const char* filename)
: d_internal(new parser_internal(tm, filename))
{
}

parser::~parser() {
  delete d_internal;
}

command* parser::parse_command() {
  return d_internal->parse_command();
}

static void sal2_lexer_reportError(pANTLR3_BASE_RECOGNIZER recognizer) {

  if (output::get_verbosity(std::cerr) > 0) {
    recognizer->displayRecognitionError(recognizer, recognizer->state->tokenNames);
  }

  // Get the actual parser
  parser_internal* parser = parser_internal::from_lexer_rec(recognizer);

  // Only report error if the parser is not already in error, otherwise
  // parser should pick it up for better error reporting
  if (!parser->parser_in_error()) {
    // Throw the exception
    std::string filename = parser->get_filename();
    int line = parser->get_current_line();
    int pos = parser->get_current_position();
    throw parser_exception("Lexer error: can't find next token.", filename, line, pos);
  }
}

static void sal2_parser_reportError(pANTLR3_BASE_RECOGNIZER recognizer) {

  if (output::get_verbosity(std::cerr) > 0) {
    recognizer->displayRecognitionError(recognizer, recognizer->state->tokenNames);
  }

  // Get the actual parser
  parser_internal* parser = parser_internal::from_parser_rec(recognizer);

  // Throw the exception
  std::string filename = parser->get_filename();
  int line = parser->get_current_line();
  int pos = parser->get_current_position();
  throw parser_exception("Parse error.", filename, line, pos);
}

}
}
