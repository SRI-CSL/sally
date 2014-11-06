/*
 * mcmtParser_state.h
 *
 *  Created on: Nov 5, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/term.h"

namespace sal2 {

namespace parser {

/** State attached to the ANTLR parser */
class mcmt_parser_state {

  expr::term_manager& d_term_manager;

public:

  mcmt_parser_state(expr::term_manager& tm)
  : d_term_manager(tm)
  {}

  expr::term_manager& tm() {
    return d_term_manager;
  }
};

}
}
