/*
 * term_pool.h
 *
 *  Created on: Oct 6, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/term.h"

#include <boost/unordered_set.hpp>

namespace sal2 {
namespace expr {

struct term_ref_with_hash {
  term_ref ref;
  size_t hash;

  term_ref_with_hash(term_ref ref, size_t hash)
  : ref(ref), hash(hash) {}
  term_ref_with_hash(const term_ref_with_hash& other)
  : ref(other.real_ref())
  , hash(other.hash)
  {}

  virtual ~term_ref_with_hash() {}

  virtual term_ref real_ref() const {
    return ref;
  }

  virtual bool cmp(const term_ref_with_hash& other) const {
    return ref == other.ref;
  }

  bool operator == (const term_ref_with_hash& ref) const;
};

/**
 * A term with all the information in the package.
 */
template <term_op op, typename iterator_type = const term_ref*>
class term_constructor : public term_ref_with_hash {

  typedef typename term_op_traits<op>::payload_type payload_type;

  /** The term manager */
  term_manager& d_tm;
  /** The payload */
  const payload_type& d_payload;
  /** The first child */
  iterator_type d_begin;
  /** One past last child */
  iterator_type d_end;

public:

  term_constructor(term_manager& tm, const payload_type& payload, iterator_type begin, iterator_type end)
  : term_ref_with_hash(term_ref(), tm.term_hash<op, iterator_type>(payload, begin, end))
  , d_tm(tm)
  , d_payload(payload)
  , d_begin(begin)
  , d_end(end)
  {}

  /** Compare to a term op without using the hash. */
  bool cmp(const term_ref_with_hash& other_ref_with_hash) const {

    term_ref other_ref = other_ref_with_hash.ref;

    // If the other reference is null, we're comparing to default => not equal
    if (other_ref.is_null()) {
      return false;
    }

    // The actual term we are comparing with
    const term& other = d_tm.term_of(other_ref);

    // Check hash first
    if (this->hash != other_ref_with_hash.hash) {
      return false;
    }

    // Different ops => not equal
    if (op != d_tm.term_of(other_ref).op()) {
      return false;
    }

    // Different sizes => not equal
    size_t size = std::distance(d_begin, d_end);
    if (size != other.size()) {
      return false;
    }

    // Compare the payloads
    if (!(d_payload == d_tm.payload_of<payload_type>(other))) {
      return false;
    }

    // Compare the children
    iterator_type it_this = d_begin;
    const term_ref* it_other = other.begin();
    for (; it_this != d_end; ++ it_this, ++ it_other) {
      if (!(*it_this == *it_other)) {
        return false;
      }
    }

    return true;
  }

  /** Actually make it happen */
  virtual term_ref real_ref() const {
    return d_tm.mk_term<op, iterator_type>(d_payload, d_begin, d_end);
  }

};

/**
 * Term references are compared directly, unless one of them is null. Null is
 * a marker that this is a term constructor, in which case the comparison is
 * done by hand.
 */
bool term_ref_with_hash::operator == (const term_ref_with_hash& other) const {
  if (this->ref.is_null()) {
    return cmp(other);
  }
  if (other.ref.is_null()) {
    return other.cmp(*this);
  }
  return cmp(other);
}


class term_pool {

public:

  struct hasher {
    size_t operator () (const term_ref_with_hash& ref) const {
      return ref.hash;
    }
  };

private:

  /** The term manager */
  term_manager& d_tm;

  /** The underlying hash set */
  typedef boost::unordered_set<term_ref_with_hash, hasher> hash_set;

  /** The pool of existing terms */
  hash_set d_pool;

public:

  term_pool(term_manager& tm)
  : d_tm(tm)
  {}

  /** Insert a new term or get a reference to an existing term that's equal. */
  template <term_op op, typename iterator_type>
  term_ref mk_term(const term_constructor<op, iterator_type>& t) {
    // Insert and return the actual term_ref
    return d_pool.insert(t).first->ref;
  }

};


}
}
