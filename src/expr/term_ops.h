/*
 * term_ops.h
 *
 *  Created on: Oct 3, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/rational.h"
#include "utils/allocator.h"

namespace sal2 {
namespace term {

enum term_type {
  TYPE_BOOL,
  TYPE_REAL,
  TYPE_INTEGER
};

/**
 * Enumeration of all term kinds.
 */
enum term_op {
  OP_VARIABLE,
  // Boolean
  OP_BOOL_CONSTANT,
  OP_AND,
  OP_OR,
  OP_NOT,
  OP_IMPLIES,
  OP_XOR,
  // Arithmetic
  OP_REAL_CONSTANT,
  OP_ADD,
  OP_SUB,
  OP_MUL,
  OP_DIV,
  OP_LAST
};

template <term_op op>
struct term_op_traits {
  typedef alloc::empty_type payload_type;
  static size_t payload_hash(const payload_type& payload) {
    return 0;
  }
};

template<>
struct term_op_traits<OP_VARIABLE> {
  typedef term_type payload_type;
  static size_t payload_hash(const payload_type& payload) {
    return payload;
  }
};

template<>
struct term_op_traits<OP_BOOL_CONSTANT> {
  typedef bool payload_type;
  static size_t payload_hash(const payload_type& payload) {
    return payload ? true : false;
  }
};

template<>
struct term_op_traits<OP_REAL_CONSTANT> {
  typedef rational payload_type;
  static size_t payload_hash(const payload_type& payload) {
    return payload.hash();
  }
};

}
}
