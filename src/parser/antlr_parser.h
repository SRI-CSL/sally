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

#pragma once

#include "parser/parser.h"
#include "expr/gc_participant.h"

#include <iostream>
#include <antlr3.h>

namespace sally {
namespace parser {

template<input_language lang>
struct antlr_parser_traits {};

template <input_language lang>
class antlr_parser : public internal_parser_interface, public expr::gc_participant {

  /** The input */
  pANTLR3_INPUT_STREAM d_input;

  /** The lexer */
  typename antlr_parser_traits<lang>::pLangLexer d_lexer;

  /** The token stream */
  pANTLR3_COMMON_TOKEN_STREAM d_token_stream;

  /** The parser */
  typename antlr_parser_traits<lang>::pLangParser d_parser;

  /** The state of the solver */
  typename antlr_parser_traits<lang>::langState d_state;

  static
  void sally_parser_reportError(pANTLR3_BASE_RECOGNIZER recognizer);

  static
  void sally_lexer_reportError(pANTLR3_BASE_RECOGNIZER recognizer);

public:

  antlr_parser(const system::context& ctx, const char* file_to_parse)
  : gc_participant(ctx.tm())
  , d_state(ctx)
  {
    // Create the input stream for the file
    d_input = antlr3FileStreamNew((pANTLR3_UINT8) file_to_parse, ANTLR3_ENC_8BIT);
    if (d_input == 0) {
      throw parser_exception(std::string("can't open ") + file_to_parse);
    }

    // Create a lexer
    d_lexer = antlr_parser_traits<lang>::newLexer(d_input);
    if (d_lexer == 0) {
      throw parser_exception("can't create the lexer");
    }

    // Report the error
    d_lexer->pLexer->rec->reportError = sally_lexer_reportError;

    // Create the token stream
    d_token_stream = antlr3CommonTokenStreamSourceNew(ANTLR3_SIZE_HINT, d_lexer->pLexer->rec->state->tokSource);
    if (d_token_stream == 0) {
      throw parser_exception("can't create the token stream");
    }

    // Create the parser
    d_parser = antlr_parser_traits<lang>::newParser(d_token_stream);
    if (d_parser == 0) {
      throw parser_exception("can't create the parser");
    }

    // Mark the internals in the super fields
    d_parser->pParser->super = this;
    d_lexer->pLexer->super = this;

    // Mark the state
    d_parser->pState = &d_state;

    // Add error reporting
    d_parser->pParser->rec->reportError = sally_parser_reportError;
  }

  ~antlr_parser() {
    d_parser->free(d_parser);
    d_token_stream->free(d_token_stream);
    d_lexer->free(d_lexer);
    d_input->free(d_input);
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

  pANTLR3_COMMON_TOKEN get_current_parser_token() const {
    pANTLR3_PARSER pParser = d_parser->pParser;
    pANTLR3_COMMON_TOKEN_STREAM cts = (pANTLR3_COMMON_TOKEN_STREAM)(pParser->tstream->super);
    return cts->tstream->_LT(cts->tstream, 1);
  }

  static
  std::string token_text(pANTLR3_COMMON_TOKEN token) {
    ANTLR3_MARKER start = token->getStartIndex(token);
    size_t size = token->getStopIndex(token) - start + 1;
    return std::string((const char*) start, size);
  }

  /** Returns the current line being parsed */
  int get_current_parser_line() const {
    pANTLR3_COMMON_TOKEN token = get_current_parser_token();
    return token->getLine(token);
  }

  /** Returns the position in the curent line that is being parsed */
  int get_current_parser_position() const {
    pANTLR3_COMMON_TOKEN token = get_current_parser_token();
    return token->getCharPositionInLine(token);
  }

  /** Returns the current line being parsed */
  int get_current_lexer_line() const {
    return d_lexer->pLexer->getLine(d_lexer->pLexer);
  }

  /** Returns the position in the curent line that is being parsed */
  int get_current_lexer_position() const {
    return d_lexer->pLexer->getCharPositionInLine(d_lexer->pLexer);
  }

  /** Get the parser from the ANTLR parser recognizer */
  static
  antlr_parser* from_parser_rec(pANTLR3_BASE_RECOGNIZER recognizer) {
    // Get the ANTLR parser
    pANTLR3_PARSER p = (pANTLR3_PARSER) recognizer->super;
    // Return the parser (stored in super)
    return (antlr_parser*) p->super;
  }

  /** Get the parser form the ANRLT lexer recognizer */
  static
  antlr_parser* from_lexer_rec(pANTLR3_BASE_RECOGNIZER recognizer) {
    // Get the ANTLR lexer
    pANTLR3_LEXER l = (pANTLR3_LEXER) recognizer->super;
    // Return the parser (stored in super)
    return (antlr_parser*) l->super;
  }

  /** Collect terms */
  void gc_collect(const expr::gc_relocator& gc_reloc);

};


template <input_language lang>
void antlr_parser<lang>::sally_lexer_reportError(pANTLR3_BASE_RECOGNIZER recognizer) {

  if (output::get_verbosity(std::cerr) > 0) {
    recognizer->displayRecognitionError(recognizer, recognizer->state->tokenNames);
  }

  // Get the actual parser
  antlr_parser* parser = antlr_parser::from_lexer_rec(recognizer);

  // Only report error if the parser is not already in error, otherwise
  // parser should pick it up for better error reporting
  if (!parser->parser_in_error()) {
    // Throw the exception
    std::string filename = parser->get_filename();
    int line = parser->get_current_lexer_line();
    int pos = parser->get_current_lexer_position();
    throw parser_exception("Lexer error.", filename, line, pos);
  }
}

template <input_language lang>
void antlr_parser<lang>::sally_parser_reportError(pANTLR3_BASE_RECOGNIZER recognizer) {

  if (output::get_verbosity(std::cerr) > 0) {
    recognizer->displayRecognitionError(recognizer, recognizer->state->tokenNames);
  }

  // Get the actual parser
  antlr_parser* parser = antlr_parser::from_parser_rec(recognizer);

  // Throw the exception
  std::string filename = parser->get_filename();
  int line = parser->get_current_parser_line();
  int pos = parser->get_current_parser_position();
  throw parser_exception("Parse error.", filename, line, pos);
}

template <input_language lang>
void antlr_parser<lang>::gc_collect(const expr::gc_relocator& gc_reloc) {
  d_state.gc_collect(gc_reloc);
}

}
}
