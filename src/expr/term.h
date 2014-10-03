/*
 * term.h
 *
 *  Created on: Oct 2, 2014
 *      Author: dejan
 */

#pragma once

#include <vector>
#include <iostream>

namespace sal2 {
namespace term {

enum output_language {
  // SMTLIB (Default)
  SMTLIB = 0
};

enum term_type {
  TYPE_BOOL,
  TYPE_REAL,
  TYPE_INTEGER
};

enum term_op {
  OP_VARIABLE,
  OP_BOOL_CONSTANT,
  OP_BOOL_AND,
  OP_BOOL_OR,
  OP_BOOL_NOT,
  OP_BOOL_IMPLIES,
  OP_BOOL_XOR
};

template <term_op op> struct term_op_traits {};

template<>
struct term_op_traits<OP_VARIABLE> {
  typedef term_type payload_type;
};

template<>
struct term_op_traits<OP_BOOL_CONSTANT> {
  typedef bool payload_type;
};

class term;
class term_ref;
class term_manager;

/** References to terms */
class term_ref {

  /** Reference into the memory */
  size_t d_ref;

  friend class term_manager;

public:

  /** Output to the stream */
  void to_stream(std::ostream& out) const;

  /** Null reference */
  static const term_ref null;
};

inline
std::ostream& operator << (std::ostream& out, const term_ref& ref) {
  ref.to_stream(out);
  return out;
}

/** Terms are an operation and children or a bayload. */
class term {

  /** The kind of term */
  term_op d_op;

  /** Additional data */
  union {
    /** Either data payload needed for constants */
    char d_payload[];
    /** Or children, including the size */
    struct {
      size_t d_size;
      term_ref d_children[];
    };
  };

  friend class term_manager;

public:

  /** Get the child */
  term_ref operator [] (size_t i) const;

  /** Get the data associated with the term */
  template <typename T>
  const T& get() const {
    return *(const T*)(&d_payload[0]);
  }

  /** Hash of the term */
  size_t hash() const;

  /** Stream it */
  void to_stream(std::ostream& out) const;

  /** Stream it */
  void to_stream_smt(std::ostream& out, const term_manager& tm) const;
};

inline
std::ostream& operator << (std::ostream& out, const term& t) {
  t.to_stream(out);
  return out;
}

class term_manager {

  /** The memory */
  char* d_memory;

  /** Used memory */
  size_t d_size;

  /** Available memory */
  size_t d_capacity;

  /** Allocate at least size bytes and return the pointer */
  term* allocate(size_t size);

public:

  /** Construct it */
  term_manager();

  template <term_op op>
  term_ref mk_term(const typename term_op_traits<op>::payload_type& payload);

  /** Make a term from one child */
  term_ref mk_term(term_op op, term_ref child);

  /** Make a term from two children */
  term_ref mk_term(term_op op, term_ref child1, term_ref child2);

  /** Make a term from children */
  term_ref mk_term(term_op op, const std::vector<term_ref>& children);

  /** Get a reference for the term */
  term_ref get_ref(const term& term) const {
    term_ref ref;
    ref.d_ref = (char*)(&term) - d_memory;
    return ref;
  }

  /** Get a term of the reference */
  const term& get_term(term_ref term_ref) const {
    return *((const term*)(d_memory + term_ref.d_ref));
  }
};

struct set_tm {
  const term_manager* tm;
  set_tm(const term_manager& tm): tm(&tm) {}
};

/** IO manipulator to set the term manager on the stream */
std::ostream& operator << (std::ostream& out, const set_tm& stm);

template <term_op op>
term_ref term_manager::mk_term(const typename term_op_traits<op>::payload_type& payload) {
  typedef typename term_op_traits<op>::payload_type payload_type;
  size_t size = sizeof(term) + sizeof(payload_type);
  term* term = allocate(size);
  term->d_op = op;
  new (term->d_payload) payload_type(payload);
  return get_ref(*term);
}

}
}
