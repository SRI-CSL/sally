/*
 * term.h
 *
 *  Created on: Oct 2, 2014
 *      Author: dejan
 */

#pragma once

#include <vector>
#include <iostream>
#include <cassert>

#include "expr/term_ops.h"
#include "utils/output.h"
#include "utils/allocator.h"
#include "utils/hash.h"

namespace sal2 {
namespace expr {

/**
 * Term manager controls the terms, allocation and garbage collection. All
 * terms are defined in term_ops.h.
 */
class term_manager {

public:

  /** Base references */
  typedef alloc::allocator_base::ref base_ref;

  /** Payload references */
  typedef base_ref payload_ref;

  /** Term references */
  class term_ref : public base_ref {
  public:
    term_ref(): base_ref() {}
    term_ref(const base_ref& ref): base_ref(ref) {}
    term_ref(const alloc::empty_type& empty) {}
    void to_stream(std::ostream& out) const;
  };

  /** Terms */
  class term {
    /** The term kind */
    term_op d_op;
    /** Hash of this term */
    size_t d_hash;
    /** Reference to the payload */
    payload_ref d_payload;

    term(): d_op(OP_LAST), d_hash(0) {}

    friend class term_manager;

  public:

    /** Construct the term with all the attributes */
    term(term_op op, size_t hash, payload_ref payload)
    : d_op(op)
    , d_hash(hash)
    , d_payload(payload)
    {}

    /** Output to the stream using the language set on the stream */
    void to_stream(std::ostream& out) const;
    /** Output to the stream using the SMT2 language */
    void to_stream_smt(std::ostream& out, const term_manager& tm) const;

    /** What kind of term is this */
    term_op op() const { return d_op; }

    /** Hash */
    size_t hash() const { return d_hash; }

    /** Number of children, if any */
    size_t size() const {
      return alloc::allocator<term, term_ref>::object_size(*this);
    }

    /** Returns the first child */
    const term_ref* begin() const {
      return alloc::allocator<term, term_ref>::object_begin(*this);
    }

    /** The one past last child */
    const term_ref* end() const {
      return alloc::allocator<term, term_ref>::object_end(*this);
    }

    /** Return the k-th child */
    term_ref operator[] (size_t k) const {
      return begin()[k];
    }
  };

private:

  /** Memory where the terms are kept */
  alloc::allocator<term, term_ref> d_memory;

  /** Memory for the payloads, one for each kind of expression */
  alloc::allocator_base* d_payload_memory[OP_LAST];

  /** List of all allocated terms */
  std::vector<term_ref> d_terms;

public:

  /** Construct them manager */
  term_manager();

  /** Destruct the manager, and destruct all payloads that the manager owns */
  ~term_manager();

  /** Compute the has of the term parts */
  template <term_op op, typename iterator_type>
  size_t term_hash(const typename term_op_traits<op>::payload_type& payload, iterator_type begin, iterator_type end);

  /** Generic term constructor */
  template <term_op op, typename iterator_type>
  term_ref mk_term(const typename term_op_traits<op>::payload_type& payload, iterator_type children_begin, iterator_type children_end);

  /** Make a term from just payload (for constants) */
  template<term_op op>
  term_ref mk_term(const typename term_op_traits<op>::payload_type& payload) {
    return mk_term<op, term_ref*>(payload, 0, 0);
  }

  /** Make a term from one child and no payload */
  template<term_op op>
  term_ref mk_term(term_ref child) {
    term_ref children[1] = { child };
    return mk_term<op, term_ref*>(alloc::empty, children, children + 1);
  }

  /** Make a term from two children and no payload */
  template<term_op op>
  term_ref mk_term(term_ref child1, term_ref child2) {
    term_ref children[2] = { child1, child2 };
    return mk_term<op, term_ref*>(alloc::empty, children, children + 2);
  }

  /** Make a term with a list of children and no payload */
  template <term_op op, typename iterator_type>
  term_ref mk_term(iterator_type children_begin, iterator_type children_end) {
    return mk_term<op, iterator_type>(alloc::empty, children_begin, children_end);
  }

  /** Get a reference for the term */
  term_ref ref_of(const term& term) const {
    return d_memory.ref_of(term);
  }

  /** Get a term of the reference */
  const term& term_of(term_ref ref) const {
    return d_memory.object_of(ref);
  }

  /** Get a term payload */
  template<typename payload_type>
  const payload_type& payload_of(const term& t) const {
    assert(d_payload_memory[t.d_op] != 0);
    return d_payload_memory[t.d_op]->object_of<payload_type>(t.d_payload);
  }

  /**
   * Get the number of children this term has.
   */
  size_t term_size(const term& t) const {
    return d_memory.object_size(t);
  }

  /** First child */
  const term_ref* term_begin(const term& t) const {
    return d_memory.object_begin(t);
  }

  /** End of children (one past) */
  const term_ref* term_end(const term& t) const {
    return d_memory.object_end(t);
  }

};

template<>
inline const alloc::empty_type& term_manager::payload_of<alloc::empty_type>(const term& t) const {
  return alloc::empty;
}


/** The term type */
typedef term_manager::term term;

/** Output operator for terms */
inline
std::ostream& operator << (std::ostream& out, const term& t) {
  t.to_stream(out);
  return out;
}

}

namespace utils {

template<>
struct hash<expr::term> {
  size_t operator()(const expr::term& t) const {
    return t.hash();
  }
};

}

namespace expr {

/** The term reference type */
typedef term_manager::term_ref term_ref;

/** Output operator for term references */
inline
std::ostream& operator << (std::ostream& out, const term_ref& t_ref) {
  t_ref.to_stream(out);
  return out;
}

/** IO modifier to set the term manager */
struct set_tm {
  const term_manager* tm;
  set_tm(const term_manager& tm): tm(&tm) {}
};

/** IO manipulator to set the term manager on the stream */
std::ostream& operator << (std::ostream& out, const set_tm& stm);

template <term_op op, typename iterator_type>
size_t term_manager::term_hash(const typename term_op_traits<op>::payload_type& payload, iterator_type begin, iterator_type end) {

  typedef typename term_op_traits<op>::payload_type payload_type;

  // Compute the hash of the term
  utils::sequence_hash hasher;
  hasher.add(op);

  // If there are children, add to the hash
  for (iterator_type it = begin; it != end; ++ it) {
    hasher.add(term_of(*it));
  }

  // If there is a payload, add it to the hash
  if (!alloc::type_traits<payload_type>::is_empty) {
    hasher.add(payload);
  }

  return hasher.get();
}

template <term_op op, typename iterator_type>
term_ref term_manager::mk_term(const typename term_op_traits<op>::payload_type& payload, iterator_type begin, iterator_type end) {

  typedef typename term_op_traits<op>::payload_type payload_type;
  typedef alloc::allocator<payload_type, alloc::empty_type> payload_allocator;

  // Construct the payload if any
  payload_ref p_ref;
  if (!alloc::type_traits<payload_type>::is_empty) {
    // If no payload allocator, construct it
    if (d_payload_memory[op] == 0) {
      d_payload_memory[op] = new payload_allocator();
    }
    // Allocate the payload and copy construct it
    payload_allocator* palloc = ((payload_allocator*) d_payload_memory[op]);
    p_ref = palloc->template allocate<alloc::empty_type_constptr>(payload, 0, 0);
  }

  // Get the hash
  size_t hash = term_hash<op, iterator_type>(payload, begin, end);

  // Construct the term
  term_ref t_ref = d_memory.allocate(term(op, hash, p_ref), begin, end);

  // Get the reference
  return t_ref;
}

}
}
