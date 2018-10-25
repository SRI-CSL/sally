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

#include <iosfwd>

#include "expr/rational.h"
#include "expr/bitvector.h"
#include "utils/allocator_types.h"
#include "utils/string.h"

namespace sally {
namespace expr {

/**
 * Enumeration of all term kinds. For each term kind, there is an associated
 * term_op_traits instantiation that defines the content of the specific kind
 * of term.
 */
enum term_op {

  // Types
  TYPE_TYPE, // Type of types
  TYPE_BOOL,
  TYPE_INTEGER,
  TYPE_REAL,
  TYPE_STRING,
  TYPE_BITVECTOR,
  TYPE_STRUCT,
  TYPE_TUPLE,
  TYPE_ENUM,
  TYPE_RECORD,
  TYPE_FUNCTION,
  TYPE_ARRAY,
  TYPE_PREDICATE_SUBTYPE,

  // Variables
  VARIABLE,

  // ITE
  TERM_ITE,

  // Equality
  TERM_EQ,

  // Boolean terms
  CONST_BOOL,
  TERM_AND,
  TERM_OR,
  TERM_NOT,
  TERM_IMPLIES,
  TERM_XOR,

  // Arithmetic terms
  CONST_RATIONAL,
  TERM_ADD,
  TERM_SUB,
  TERM_MUL,
  TERM_DIV,
  TERM_MOD,
  TERM_LEQ,
  TERM_LT,
  TERM_GEQ,
  TERM_GT,
  TERM_TO_INT,
  TERM_TO_REAL,
  TERM_IS_INT,

  // Bit-vector terms
  CONST_BITVECTOR,
  TERM_BV_ADD,
  TERM_BV_SUB,
  TERM_BV_MUL,
  TERM_BV_UDIV, // NOTE: semantics of division is x/0 = 111...111
  TERM_BV_SDIV,
  TERM_BV_UREM,
  TERM_BV_SREM,
  TERM_BV_SMOD,
  TERM_BV_XOR,
  TERM_BV_SHL,
  TERM_BV_LSHR,
  TERM_BV_ASHR,
  TERM_BV_NOT,
  TERM_BV_AND,
  TERM_BV_OR,
  TERM_BV_NAND,
  TERM_BV_NOR,
  TERM_BV_XNOR,
  TERM_BV_CONCAT,
  TERM_BV_EXTRACT,
  TERM_BV_ULEQ,
  TERM_BV_SLEQ,
  TERM_BV_ULT,
  TERM_BV_SLT,
  TERM_BV_UGEQ,
  TERM_BV_SGEQ,
  TERM_BV_UGT,
  TERM_BV_SGT,
  TERM_BV_SGN_EXTEND,

  // Arrays
  TERM_ARRAY_READ,
  TERM_ARRAY_WRITE,
  TERM_ARRAY_LAMBDA,

  // Tuples
  TERM_TUPLE_CONSTRUCT,
  TERM_TUPLE_READ,
  TERM_TUPLE_WRITE,

  // Enum constants
  CONST_ENUM,

  // Records
  TERM_RECORD_CONSTRUCT,
  TERM_RECORD_READ,
  TERM_RECORD_WRITE,

  // Abstractions
  TERM_LAMBDA,
  TERM_EXISTS,
  TERM_FORALL,

  // Function application
  TERM_FUN_APP,

  // Constant strings
  CONST_STRING,

  // Marker for the last
  OP_LAST
};

/** Output operator */
std::ostream& operator << (std::ostream& out, term_op op);

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
 * Bitvector types have a payload of type size_t > 0.
 */
template<>
struct term_op_traits<TYPE_BITVECTOR> {
  typedef size_t payload_type;
};

/**
 * Bitvector extract.
 */
template<>
struct term_op_traits<TERM_BV_EXTRACT> {
  typedef expr::bitvector_extract payload_type;
};

/**
 * Bitvector sign extend.
 */
template<>
struct term_op_traits<TERM_BV_SGN_EXTEND> {
  typedef expr::bitvector_sgn_extend payload_type;
};

/**
 * Boolean constant terms have a payload of type bool and no children.
 */
template<>
struct term_op_traits<CONST_BOOL> {
  typedef bool payload_type;
};

/**
 * Rational constants terms have a payload of type rational (gmp) and no children.
 */
template<>
struct term_op_traits<CONST_RATIONAL> {
  typedef rational payload_type;
};

/**
 * Bitvector constants have a payload of type bitvector.
 */
template<>
struct term_op_traits<CONST_BITVECTOR> {
  typedef bitvector payload_type;
};

/**
 * Enumeration constants have a payload of type size_t (index).
 */
template<>
struct term_op_traits<CONST_ENUM> {
  typedef size_t payload_type;
};

/**
 * Variables have a payload that is their name, and one child, which is the
 * type of the variable.
 */
template<>
struct term_op_traits<VARIABLE> {
  typedef utils::string payload_type;
};

/**
 * Tuple access, payload is the index.
 */
template<>
struct term_op_traits<TERM_TUPLE_READ> {
  typedef size_t payload_type;
};

/**
 * Tuple write, payload is the index.
 */
template<>
struct term_op_traits<TERM_TUPLE_WRITE> {
  typedef size_t payload_type;
};


/**
 * Strings just have string payloads.
 */
template<>
struct term_op_traits<CONST_STRING> {
  typedef utils::string payload_type;
};

}
}
