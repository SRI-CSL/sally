/*
 * term_manager_internal_internal.h
 *
 *  Created on: Nov 17, 2014
 *      Author: dejan
 */

#pragma once

#include "expr/term.h"
#include "utils/allocator.h"

#include <boost/unordered_map.hpp>
#include <boost/unordered_set.hpp>

#include <map>
#include <queue>
#include <iterator>

namespace sal2 {
namespace expr {

/**
 * References with additional data, mainly for internal term manager use.
 */
class term_ref_fat : public term_ref {

protected:

  /** Id of the term in the expression manager */
  size_t d_id;

  /** Hash of the term */
  size_t d_hash;

  friend class term_manager_internal;

  term_ref_fat(const term_ref& ref, size_t id, size_t hash)
  : term_ref(ref), d_id(id), d_hash(hash) {}

public:

  /** Construct null reference */
  term_ref_fat()
  : term_ref(), d_id(0), d_hash(0) {}
  /** Construct a copy, while finalizing the other reference if needed */
  term_ref_fat(const term_ref_fat& other) {
    *this = other.finalize();
  }

  virtual ~term_ref_fat() {}

  /** Return the "real" version of self. Default, just self. */
  virtual term_ref_fat finalize() const {
    return term_ref_fat(*this, d_id, d_hash);
  }

  /** The ID of the term. Doesn't change during lifetime */
  size_t id() const { return d_id; }

  /** Returns the hash of the reference */
  size_t hash() const { return d_hash; }

  /** By default we compare with references */
  virtual bool cmp(const term_ref_fat& other) const {
    assert(index() != 0);
    assert(other.index() != 0);
    return index() == other.index();
  }

  /** Comparison with cmp. If any is null, we use it for this->cmp */
  bool operator == (const term_ref_fat& ref) const;
};

/**
 * Term manager controls the terms, allocation and garbage collection. All
 * terms are defined in term_ops.h.
 */
class term_manager_internal {

public:

  /** Base references */
  typedef alloc::ref base_ref;

  /** Payload references */
  typedef base_ref payload_ref;

  struct term_ref_fat_hasher {
    size_t operator () (const term_ref_fat& ref) const {
      return ref.hash();
    }
  };

  /**
   * A term with all the information in the package.
   */
  template <term_op op, typename iterator_type>
  class term_ref_constructor : public term_ref_fat {

    typedef typename term_op_traits<op>::payload_type payload_type;

    /** The payload */
    const payload_type& d_payload;
    /** The first child */
    iterator_type d_begin;
    /** One past last child */
    iterator_type d_end;

    term_manager_internal& d_tm;

  public:

    term_ref_constructor(term_manager_internal& tm, const payload_type& payload, iterator_type begin, iterator_type end)
    : term_ref_fat(term_ref(), 0, tm.term_hash<op, iterator_type>(payload, begin, end))
    , d_payload(payload)
    , d_begin(begin)
    , d_end(end)
    , d_tm(tm)
    {}

    /** Compare to a term op without using the hash. */
    bool cmp(const term_ref_fat& other_ref) const;

    /**
     * Actually construct the reference. This is remembered and guarded from
     * calling more than once.
     */
    virtual term_ref_fat finalize() const {
      return d_tm.mk_term_internal<op, iterator_type>(d_payload, d_begin, d_end, d_hash);
    }

  };

private:

  /** Whether to typecheck or not */
  bool d_typecheck;

  /** Memory where the terms are kept */
  alloc::allocator<term, term_ref> d_memory;

  /** Memory for the payloads, one for each kind of expression */
  alloc::allocator_base* d_payload_memory[OP_LAST];

  /** Generic term constructor */
  template <term_op op, typename iterator_type>
  term_ref_fat mk_term_internal(const typename term_op_traits<op>::payload_type& payload, iterator_type children_begin, iterator_type children_end, size_t hash);

  /** The underlying hash set */
  typedef boost::unordered_set<term_ref_fat, term_ref_fat_hasher> term_ref_hash_set;

  /** The pool of existing terms */
  term_ref_hash_set d_pool;

  typedef boost::unordered_map<term_ref, term_ref, term_ref_hasher> tcc_map;

  /**
   * Map from terms to their type-checking conditions. If the entry is empty
   * then TCC = true.
   */
  tcc_map d_tcc_map;

  /** Type-check the term (adds to TCC if needed) */
  bool typecheck(term_ref t);

  /** Compute the hash of the term parts */
  template <term_op op, typename iterator_type>
  size_t term_hash(const typename term_op_traits<op>::payload_type& payload, iterator_type begin, iterator_type end);

  typedef boost::unordered_map<term_ref, size_t, term_ref_hasher> tref_id_map;

  /** Map from term references to their ids */
  tref_id_map d_term_ids;

  /** Reference counts */
  std::vector<size_t> d_term_refcount;

  friend class term_ref_strong;

  void attach(size_t id) {
    d_term_refcount[id] ++;
  }

  void detach(size_t id) {
    assert(d_term_refcount[id] > 0);
    d_term_refcount[id] --;
  }

  /** Get a new id of the term */
  size_t new_term_id() {
    size_t id = d_term_refcount.size();
    d_term_refcount.push_back(0);
    return id;
  }

  //
  // These below should be last, so that they are destructed first
  //

  /** Boolean type */
  term_ref_strong d_booleanType;

  /** Integer type */
  term_ref_strong d_integerType;

  /** Real type */
  term_ref_strong d_realType;

  typedef std::map<size_t, term_ref_strong> bitvector_type_map;

  /** The bitvector types */
  bitvector_type_map d_bitvectorType;

  /** Prefixes to be removed when printing variable names */
  std::vector<std::string> d_namespaces;

public:

  /** Construct them manager */
  term_manager_internal(bool typecheck);

  /** Destruct the manager, and destruct all payloads that the manager owns */
  ~term_manager_internal();

  /** Print the term manager information and all the terms to out */
  void to_stream(std::ostream& out) const;

  /** Get the Boolean type */
  term_ref booleanType() const { return d_booleanType; }

  /** Get the Integer type */
  term_ref integerType() const { return d_integerType; }

  /** Get the Real type */
  term_ref realType() const { return d_realType; }

  /** Get the Bitvector type */
  term_ref bitvectorType(size_t size);

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
    return mk_term<op, term_ref*>(alloc::empty_type(), children, children + 1);
  }

  /** Make a term from two children and no payload */
  template<term_op op>
  term_ref mk_term(term_ref child1, term_ref child2) {
    term_ref children[2] = { child1, child2 };
    return mk_term<op, term_ref*>(alloc::empty_type(), children, children + 2);
  }

  /** Make a term with a list of children and no payload */
  template <term_op op, typename iterator_type>
  term_ref mk_term(iterator_type children_begin, iterator_type children_end) {
    return mk_term<op, iterator_type>(alloc::empty_type(), children_begin, children_end);
  }

  /** Make a term from one child and payload */
  template<term_op op>
  term_ref mk_term(const typename term_op_traits<op>::payload_type& payload, term_ref child) {
    term_ref children[1] = { child };
    return mk_term<op, term_ref*>(payload, children, children + 1);
  }

  /** Make a term from two children and payload */
  template<term_op op>
  term_ref mk_term(const typename term_op_traits<op>::payload_type& payload, term_ref child1, term_ref child2) {
    term_ref children[2] = { child1, child2 };
    return mk_term<op, term_ref*>(payload, children, children + 2);
  }

  /** Make a term, given children */
  template <typename iterator>
  term_ref mk_term(term_op op, iterator begin, iterator end);

  /** Get a reference for the term */
  term_ref ref_of(const term& term) const {
    return d_memory.ref_of(term);
  }

  /** Get a term of the reference */
  const term& term_of(const term_ref& ref) const {
    return d_memory.object_of(ref);
  }

  /** Get a term payload */
  template<typename payload_type>
  const payload_type& payload_of(const term& t) const {
    assert(d_payload_memory[t.d_op] != 0);
    return d_payload_memory[t.d_op]->object_of<payload_type>(*t.end());
  }

  /** Get a term payload */
  template<typename payload_type>
  const payload_type& payload_of(term_ref t_ref) const {
    const term& t = term_of(t_ref);
    return payload_of<payload_type>(t);
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

  /** Get the type of the term */
  term_ref type_of(const term& t) const;

  /** Get the type of the term */
  term_ref type_of(term_ref t) const {
    return type_of(term_of(t));
  }

  /** Get the TCC of the term */
  term_ref tcc_of(const term& t) const;

  /** Get the TCC of the term */
  term_ref tcc_of(const term_ref& t) const {
    return tcc_of(term_of(t));
  }

  /** Get the id of the term */
  size_t id_of(term_ref ref) const {
    if (ref.is_null()) return 0;
    assert(d_term_ids.find(ref) != d_term_ids.end());
    return d_term_ids.find(ref)->second;
  }

  /** Get the hash of the term */
  size_t hash_of(term_ref ref) const {
    if (ref.is_null()) return 0;
    return term_of(ref).hash();
  }

  /** Get the string representation of the term */
  std::string to_string(term_ref ref) const;

  /** Add a namespace entry (will be removed from prefix when printing. */
  void use_namespace(std::string ns);

  /** Pop the last added namespace */
  void pop_namespace();

  /** Return the subterms what return true on m(t) */
  template<typename collection, typename matcher>
  void get_subterms(term_ref t, const matcher& m, collection& out);

  /** Map of substitutions */
  typedef boost::unordered_map<term_ref, term_ref, term_ref_hasher> substitution_map;

  /** Return t with subst applied */
  term_ref substitute(term_ref t, substitution_map& subst);

  /** Returns the id normalized with resepct to the current namespaces */
  std::string namespace_normalize(std::string id) const;
};

inline
std::ostream& operator << (std::ostream& out, const term_manager_internal& tm) {
  tm.to_stream(out);
  return out;
}

template<>
inline const alloc::empty_type& term_manager_internal::payload_of<alloc::empty_type>(const term& t) const {
  static alloc::empty_type empty;
  return empty;
}

template <term_op op, typename iterator_type>
size_t term_manager_internal::term_hash(const typename term_op_traits<op>::payload_type& payload, iterator_type begin, iterator_type end) {

  typedef typename term_op_traits<op>::payload_type payload_type;

  // Compute the hash of the term
  utils::sequence_hash hasher;
  hasher.add(op);

  // If there are children, add to the hash
  for (iterator_type it = begin; it != end; ++ it) {
    hasher.add(term_of(*it).hash());
  }

  // If there is a payload, add it to the hash
  if (!alloc::type_traits<payload_type>::is_empty) {
    hasher.add(payload);
  }

  return hasher.get();
}

template <term_op op, typename iterator_type>
term_ref_fat term_manager_internal::mk_term_internal(const typename term_op_traits<op>::payload_type& payload, iterator_type begin, iterator_type end, size_t hash) {

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
    p_ref = palloc->template allocate<alloc::empty_type*>(payload, 0, 0, 0);
  }

  // Construct the term
  term_ref t_ref;
  if (alloc::type_traits<payload_type>::is_empty) {
    // No payload, 0 for extras
    t_ref = d_memory.allocate(term(op, hash), begin, end, 0);
  } else {
    // Pyaload active, add a child
    t_ref = d_memory.allocate(term(op, hash), begin, end, 1);
    *alloc::allocator<term, term_ref>::object_end(d_memory.object_of(t_ref)) = p_ref;
  }

  // Type-check the term
  if (d_typecheck) {
    if (!typecheck(t_ref)) {
      return term_ref_fat();
    }
  }

  // Set the id of the term and add to terms
  size_t id = new_term_id();
  d_term_ids[t_ref] = id;


  // Get the reference
  return term_ref_fat(t_ref, id, hash);
}

template <term_op op, typename iterator_type>
term_ref term_manager_internal::mk_term(const typename term_op_traits<op>::payload_type& payload, iterator_type begin, iterator_type end) {
  // Insert and return the actual term_ref
  term_ref_fat fat_ref = *d_pool.insert(term_ref_constructor<op, iterator_type>(*this, payload, begin, end)).first;
  return fat_ref;
}

/** Compare to a term op without using the hash. */
template <term_op op, typename iterator_type>
bool term_manager_internal::term_ref_constructor<op, iterator_type>::cmp(const term_ref_fat& other_ref) const {

  // If the other reference is null, we're comparing to default => not equal
  if (other_ref.is_null()) {
    return false;
  }

  // Compare hashes first
  if (hash() != other_ref.hash()) {
    return false;
  }

  // The actual term we are comparing with
  const term& other = d_tm.term_of(other_ref);

  // Different ops => not equal
  if (op != d_tm.term_of(other_ref).op()) {
    return false;
  }

  // Variables are always different, even variables with the same name
  if (op == VARIABLE) {
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
    if (it_this->index() != it_other->index()) {
      return false;
    }
  }

  return true;
}


template <typename iterator>
term_ref term_manager_internal::mk_term(term_op op, iterator begin, iterator end) {

  term_ref result;

#define SWITCH_TO_TERM(OP) case OP: result = mk_term<OP>(begin, end); break;

  // Only needed for the kinds that can be constructed with an op and children
  switch (op) {
    SWITCH_TO_TERM(TERM_EQ)
    SWITCH_TO_TERM(TERM_ITE)
    SWITCH_TO_TERM(TERM_AND)
    SWITCH_TO_TERM(TERM_OR)
    SWITCH_TO_TERM(TERM_NOT)
    SWITCH_TO_TERM(TERM_IMPLIES)
    SWITCH_TO_TERM(TERM_XOR)
    SWITCH_TO_TERM(TERM_ADD)
    SWITCH_TO_TERM(TERM_SUB)
    SWITCH_TO_TERM(TERM_MUL)
    SWITCH_TO_TERM(TERM_DIV)
    SWITCH_TO_TERM(TERM_LEQ)
    SWITCH_TO_TERM(TERM_LT)
    SWITCH_TO_TERM(TERM_GEQ)
    SWITCH_TO_TERM(TERM_GT)
    SWITCH_TO_TERM(TERM_BV_ADD)
    SWITCH_TO_TERM(TERM_BV_SUB)
    SWITCH_TO_TERM(TERM_BV_MUL)
    SWITCH_TO_TERM(TERM_BV_U_LEQ)
    SWITCH_TO_TERM(TERM_BV_S_LEQ)
    SWITCH_TO_TERM(TERM_BV_U_LT)
    SWITCH_TO_TERM(TERM_BV_S_LT)
    SWITCH_TO_TERM(TERM_BV_U_GEQ)
    SWITCH_TO_TERM(TERM_BV_S_GEQ)
    SWITCH_TO_TERM(TERM_BV_U_GT)
    SWITCH_TO_TERM(TERM_BV_S_GT)
    SWITCH_TO_TERM(TERM_BV_XOR)
    SWITCH_TO_TERM(TERM_BV_SHL)
    SWITCH_TO_TERM(TERM_BV_LSHR)
    SWITCH_TO_TERM(TERM_BV_ASHR)
    SWITCH_TO_TERM(TERM_BV_NOT)
    SWITCH_TO_TERM(TERM_BV_AND)
    SWITCH_TO_TERM(TERM_BV_OR)
    SWITCH_TO_TERM(TERM_BV_NAND)
    SWITCH_TO_TERM(TERM_BV_NOR)
    SWITCH_TO_TERM(TERM_BV_XNOR)
  default:
    assert(false);
  }

#undef SWITCH_TO_TERM

  return result;
}

template<typename collection, typename matcher>
void term_manager_internal::get_subterms(term_ref t, const matcher& m, collection& out) {
  typedef boost::unordered_set<term_ref, term_ref_hasher> visited_set;

  visited_set v;
  std::queue<term_ref> queue;
  queue.push(t);

  std::insert_iterator<collection> insert(out, out.end());

  while (!queue.empty()) {

    // Process current
    term_ref current = queue.front();
    queue.pop();
    if (m(term_of(current))) {
      *insert = current;
    }

    // Add any unvisited children
    const term& current_term = term_of(current);
    for (size_t i = 0; i < current_term.size(); ++ i) {
      if (v.find(current_term[i]) == v.end()) {
        queue.push(current_term[i]);
      }
    }
  }
}

}
}
