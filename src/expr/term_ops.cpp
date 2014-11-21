/*
 * term_ops.cpp
 *
 *  Created on: Nov 21, 2014
 *      Author: dejan
 */

#include "expr/term_ops.h"

#include <iostream>

namespace sal2 {
namespace expr {

std::ostream& operator << (std::ostream& out, term_op op) {

#define SWITCH_TO_STRING(op) case op: out << #op; break;
  switch (op) {
    SWITCH_TO_STRING(TYPE_BOOL)
    SWITCH_TO_STRING(TYPE_INTEGER)
    SWITCH_TO_STRING(TYPE_REAL)
    SWITCH_TO_STRING(TYPE_STRUCT)
    SWITCH_TO_STRING(VARIABLE)
    SWITCH_TO_STRING(TERM_EQ)
    SWITCH_TO_STRING(TERM_ITE)
    SWITCH_TO_STRING(CONST_BOOL)
    SWITCH_TO_STRING(TERM_AND)
    SWITCH_TO_STRING(TERM_OR)
    SWITCH_TO_STRING(TERM_NOT)
    SWITCH_TO_STRING(TERM_IMPLIES)
    SWITCH_TO_STRING(TERM_XOR)
    SWITCH_TO_STRING(CONST_RATIONAL)
    SWITCH_TO_STRING(TERM_ADD)
    SWITCH_TO_STRING(TERM_SUB)
    SWITCH_TO_STRING(TERM_MUL)
    SWITCH_TO_STRING(TERM_DIV)
    SWITCH_TO_STRING(TERM_LEQ)
    SWITCH_TO_STRING(TERM_LT)
    SWITCH_TO_STRING(TERM_GEQ)
    SWITCH_TO_STRING(TERM_GT)
    SWITCH_TO_STRING(CONST_STRING);
    SWITCH_TO_STRING(OP_LAST)
  default:
    out << "unknown";
  }
#undef SWITCH_TO_STRING
  return out;
}

}
}
