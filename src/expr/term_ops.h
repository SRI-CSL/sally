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
namespace expr {

enum term_type {
  TYPE_BOOL,
  TYPE_REAL,
  TYPE_INTEGER
};

/**
 * Enumeration of all term kinds. For each term kind, there is an associated
 * term_op_traits instantiation that defines the content of the specific kind
 * of term.
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

/**
 * The traits class contains an instantiation for each term kind. Any payload
 * types need to have an associated utils::hash specialization, copy constructors
 * and the operator ==.
 *
 * If the term has a payload it should define the payload_type to be of that
 * type, or otherwise define it to be alloc::empty_type.
 */
template <term_op op>
struct term_op_traits {
  /** Default terms have no payload, so we use the alloc::empty type. */
  typedef alloc::empty_type payload_type;
};

/**
 * Boolean constant terms have a payload of type bool and no children.
 */
template<>
struct term_op_traits<OP_BOOL_CONSTANT> {
  typedef bool payload_type;
};

/**
 * Rational constants terms have a payload of type rational (gmp) and no children.
 */
template<>
struct term_op_traits<OP_REAL_CONSTANT> {
  typedef rational payload_type;
};

template<>
struct term_op_traits<OP_VARIABLE> {
  typedef term_type payload_type;
};

}
}
