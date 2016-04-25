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

#include <map>
#include <vector>
#include <cassert>
#include <iosfwd>

#include "expr/term_ops.h"

#include "utils/hash.h"
#include "utils/output.h"
#include "utils/allocator_types.h"

namespace sally {
namespace expr {

// Forward declaration
class term_manager;
class term_manager_internal;
class term_ref_strong;

/** Term references */
class term_ref : public alloc::ref {
  typedef alloc::ref base_ref;
public:
  term_ref(): base_ref() {}
  term_ref(const base_ref& ref): base_ref(ref) {}
  term_ref(const alloc::empty_type& empty) {}
  void to_stream(std::ostream& out) const;

  bool operator < (const term_ref& ref) const { return index() < ref.index(); }
  bool operator > (const term_ref& ref) const { return index() > ref.index(); }
  bool operator == (const term_ref& ref) const { return index() == ref.index(); }
};

/**
 * Hasher for term references.
 * Do not use for permanent caches unless you plan to do garbage collection
 * manually.
 */
struct term_ref_hasher {
  size_t operator () (const term_ref& ref) const {
    return ref.index();
  }
};

/** Output operator for term references */
inline
std::ostream& operator << (std::ostream& out, const term_ref& t_ref) {
  t_ref.to_stream(out);
  return out;
}

/**
 * Strong reference that also does reference counting.
 */
class term_ref_strong : public term_ref {

    /** Responsible term manager */
    term_manager_internal* d_tm;

    friend class term_manager;

  public:

    /** Construct null reference */
    term_ref_strong()
    : term_ref(), d_tm(0) {}

    /** Construct a copy */
    term_ref_strong(const term_ref_strong& other);

    /** Construct from a weak reference */
    term_ref_strong(term_manager_internal& tm, term_ref ref);

    /** Construct from a weak reference */
    term_ref_strong(term_manager& tm, term_ref ref);

    /** Destruct */
    ~term_ref_strong();

    /** Assignment */
    term_ref_strong& operator = (const term_ref_strong& other);

    /** Hash of the term */
    size_t hash() const;

    /** Id of the term */
    size_t id() const;
};

/** Hashing for terms. */
struct term_ref_strong_hasher {
  size_t operator () (const term_ref_strong& ref) const {
    return ref.hash();
  }
};

/** Terms */
class term {

  typedef alloc::ref payload_ref;

  /** The term kind */
  term_op d_op;

  /** The hash of the term (independent of reference) */
  size_t d_hash;

  /** Default constructor */
  term(): d_op(OP_LAST), d_hash(0) {}

  /** Construct the term with all the attributes */
  term(term_op op, size_t hash)
  : d_op(op), d_hash(hash) {}

  friend class term_manager_internal;

public:

  typedef std::map<expr::term_ref, std::string> expr_let_cache;

  /** Collect the cache of let definitions */
  void mk_let_cache(term_manager& tm, expr_let_cache& let_cache, std::vector<expr::term_ref>& definitions) const;

  /** Output to the stream using the SMT2 language */
  void to_stream_smt_with_let(std::ostream& out, term_manager& tm, const expr_let_cache& let_cache, const std::vector<expr::term_ref>& definitions, int level = 0) const;

  /** Output to the stream using the SMT2 language */
  void to_stream_smt_without_let(std::ostream& out, term_manager& tm, const expr_let_cache& let_cache, bool use_cache_on_root = true, int level = 0) const;

  /** Output to the stream using the NUXMV language */
  void to_stream_nuxmv_without_let(std::ostream& out, term_manager& tm, const expr_let_cache& let_cache, bool use_cache_on_root = true, int level = 0) const;

  /** Output to the stream using the language set on the stream */
  void to_stream(std::ostream& out) const;

  /** What kind of term is this */
  term_op op() const { return d_op; }

  /** Returns the hash of the term */
  size_t hash() const { return d_hash; }

  /** Number of children, if any */
  size_t size() const;

  /** Returns the first child */
  const term_ref* begin() const;

  /** The one past last child */
  const term_ref* end() const;

  /** Return the k-th child */
  term_ref operator[] (size_t k) const {
    return begin()[k];
  }

  /** Return the k-th child */
  term_ref child(size_t k) const {
    return begin()[k];
  }

};

/** Output operator for terms */
inline
std::ostream& operator << (std::ostream& out, const term& t) {
  t.to_stream(out);
  return out;
}

}
}
