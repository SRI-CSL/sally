/*
 * term.h
 *
 *  Created on: Oct 2, 2014
 *      Author: dejan
 */

#pragma once

#include <vector>
#include <iostream>

#include "expr/term_ops.h"
#include "utils/output.h"
#include "utils/allocator.h"

namespace sal2 {
namespace term {

class term;
class term_manager;

/** References to terms */
class term_ref {

  /** Reference into the memory */
  size_t d_ref;

  /** Private only to internal classes */
  term_ref(size_t ref): d_ref(ref) {}

  friend class term;
  friend class term_manager;

public:

  /** Default ref construct a null reference */
  term_ref(): d_ref(-1) {}
  /** Copy constructor */
  term_ref(const term_ref& tref): d_ref(tref.d_ref) {}
  /** Assignment */
  term_ref& operator = (const term_ref& tref) { d_ref = tref.d_ref; return *this; }

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

  /** The extra data reference */
  size_t d_extras_ref;

  /** Number of children */
  size_t d_size;

  /** The children */
  term_ref d_children[];

  friend class term_manager;

  /** Size in bytes necessary for the term */
  static size_t alloc_size(size_t nchildren) {
    return sizeof(term) + nchildren * sizeof(term_ref);
  }

public:

  /** Construct the term */
  template<typename iterator_type>
  void construct(term_op op, iterator_type begin, iterator_type end) {
    d_op = op;
    d_size = end - begin;
    for (size_t i = 0; begin != end; ++ i, ++ begin) {
      d_children[i] = *begin;
    }
  }

  /** Get the child */
  term_ref operator [] (size_t i) const;

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

/** Extra data of the term */
struct term_extra {
  /** Hash of the term */
  size_t d_hash;
  /** Any payload */
  char d_data[];

  template<typename T>
  void construct(size_t hash, const T* payload) {
    d_hash = hash;
    new (d_data) T(*payload);
  }

  template<typename T>
  static size_t alloc_size() { return sizeof(term_extra) + sizeof(T); }

  template<typename T>
  const T& get() const { return *(const T*)d_data; }

  template<typename T>
  T& get() { return *(T*)d_data; }
};

class term_manager {

  /** Memory for the terms */
  utils::allocator d_term_memory;

  /** Memory for the extras */
  utils::allocator d_term_extra_memory;

  /** All allocated terms */
  std::vector<term_ref> d_terms;

  /** Compute the hash of the term */
  size_t compute_hash(const term* t);

public:

  /** Destruct it */
  ~term_manager();

  /** Generic term constructor */
  template <term_op op, typename iterator_type>
  term_ref mk_term(const typename term_op_traits<op>::payload_type& payload, iterator_type children_begin, iterator_type children_end);

  /** Make a term from just payload */
  template<term_op op>
  term_ref mk_term(const typename term_op_traits<op>::payload_type& payload) {
    return mk_term<op, char*>(payload, 0, 0);
  }

  /** Make a term from one child */
  template<term_op op>
  term_ref mk_term(term_ref child) {
    term_ref children[1] = { child };
    return mk_term<op, term_ref*>(payload_null, children, children + 1);
  }

  /** Make a term from two children */
  template<term_op op>
  term_ref mk_term(term_ref child1, term_ref child2) {
    term_ref children[2] = { child1, child2 };
    return mk_term<op, term_ref*>(payload_null, children, children + 2);
  }

  /** Make a term with a list of children */
  template <term_op op, typename iterator_type>
  term_ref mk_term(iterator_type children_begin, iterator_type children_end) {
    return mk_term<op, iterator_type>(payload_null, children_begin, children_end);
  }

  /** Get a reference for the term */
  term_ref get_ref(const term& term) const {
    return term_ref(d_term_memory.index_of(&term));
  }

  /** Get a term of the reference */
  const term& get_term(term_ref term_ref) const {
    return d_term_memory.get<term>(term_ref.d_ref);
  }

  /** Get a term extra */
  const term_extra& get_term_extra(const term* t) const {
    return d_term_extra_memory.get<term_extra>(t->d_extras_ref);
  }


};

struct set_tm {
  const term_manager* tm;
  set_tm(const term_manager& tm): tm(&tm) {}
};

/** IO manipulator to set the term manager on the stream */
std::ostream& operator << (std::ostream& out, const set_tm& stm);

template <term_op op, typename iterator_type>
term_ref term_manager::mk_term(const typename term_op_traits<op>::payload_type& payload, iterator_type begin, iterator_type end) {
  typedef typename term_op_traits<op>::payload_type payload_type;
  // Compute the hash
  size_t hash = op;
  for (iterator_type it = begin; it != end; ++ it) {
    hash ^= d_term_extra_memory.get<term_extra>(get_term(*it).d_extras_ref).d_hash + 0x9e3779b9 + (hash << 6) + (hash >> 2);
  }
  hash ^= term_op_traits<op>::payload_hash(payload);
  // Construct the term
  term* t = d_term_memory.allocate<term>(term::alloc_size(end - begin));
  t->construct(op, begin, end);
  // Construct the payload
  term_extra* t_extra = d_term_extra_memory.allocate<term_extra>(term_extra::alloc_size<payload_type>());
  t_extra->construct<payload_type>(hash, &payload);
  // Get the reference
  return term_ref(d_term_memory.index_of(t));
}

}
}
