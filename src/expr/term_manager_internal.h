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

#include "expr/term.h"
#include "utils/allocator.h"
#include "utils/name_transformer.h"
#include "utils/statistics.h"

#include <boost/unordered_map.hpp>
#include <boost/unordered_set.hpp>

#include <map>
#include <queue>
#include <iterator>

namespace sally {
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

  typedef boost::unordered_map<term_ref, term_ref, term_ref_hasher> term_to_term_map;

  /** Map from term to their types. It's built on demand. */
  term_to_term_map d_type_cache;

  /** Map from the to their base types. It's build on demand. */
  term_to_term_map d_base_type_cache;

  /**
   * Map from terms to their type-checking conditions. If the entry is empty
   * then TCC = true.
   */
  term_to_term_map d_tcc_map;

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

  /** The type of types */
  term_ref_strong d_typeType;

  /** Boolean type */
  term_ref_strong d_booleanType;

  /** Integer type */
  term_ref_strong d_integerType;

  /** Real type */
  term_ref_strong d_realType;

  /** String type */
  term_ref_strong d_stringType;

  typedef std::map<size_t, term_ref_strong> bitvector_type_map;

  /** The bitvector types */
  bitvector_type_map d_bitvectorType;

  /** Prefixes to be removed when printing variable names */
  std::vector<std::string> d_namespaces;

  /** Name transformers */
  const utils::name_transformer* d_name_transformer;

  utils::stat_int* d_stat_terms;

  /** Compute the type of t and all subterms */
  void compute_type(term_ref t);

public:

  /** Construct them manager */
  term_manager_internal(utils::statistics& stats);

  /** Destruct the manager, and destruct all payloads that the manager owns */
  ~term_manager_internal();

  /** Print the term manager information and all the terms to out */
  void to_stream(std::ostream& out) const;

  /** Type-check the term */
  void typecheck(term_ref t);

  /** Get the type of types */
  term_ref type_type() const { return d_typeType; }

  /** Get the Boolean type */
  term_ref boolean_type() const { return d_booleanType; }

  /** Get the Integer type */
  term_ref integer_type() const { return d_integerType; }

  /** Get the Real type */
  term_ref real_type() const { return d_realType; }

  /** Get the String type */
  term_ref string_type() const  { return d_stringType; }

  /** Get the Bitvector type */
  term_ref bitvector_type(size_t size);

  /** Is t the bitvector type */
  bool is_bitvector_type(term_ref t) const;

  /** Make a function type (t1, t2, ..., tn), with ti being types, tn being co-domain */
  term_ref function_type(const std::vector<term_ref>& args);

  /** Is t a function type */
  bool is_function_type(term_ref t) const;

  /** Check if this is an integer type */
  bool is_integer_type(term_ref t) const;

  /** Check if this is a real type */
  bool is_real_type(term_ref t) const;

  /** Is this a type */
  static
  bool is_type(const term& t);

  /** Is this a primitive type */
  static
  bool is_primitive_type(const term& t);

  /** Is this a type */
  bool is_type(term_ref t) const { return is_type(term_of(t)); }

  /** Is this a primitive type */
  bool is_primitive_type(term_ref t) const { return is_primitive_type(term_of(t)); }

  /** Get the domain type of a function type */
  term_ref get_function_type_domain(term_ref fun_type, size_t i) const;

  /** Get the co-domain type of a function type */
  term_ref get_function_type_codomain(term_ref fun_type) const;

  /** Make an array type t1 -> t2 */
  term_ref array_type(term_ref index_type, term_ref element_type);

  /** Is t an array type */
  bool is_array_type(term_ref t) const;

  /** Get the index type of the array type */
  term_ref get_array_type_index(term_ref arr_type) const;

  /** Get the element type of the array type */
  term_ref get_array_type_element(term_ref arr_type) const;

  /** Make a tuple type (t1, t2, ..., tn) with ti being types */
  term_ref tuple_type(const std::vector<term_ref>& args);

  /** Is t a tuple type */
  bool is_tuple_type(term_ref t) const;

  /** Get the k-th element of the tuple type */
  term_ref get_tuple_type_element(term_ref tuple_type, size_t i) const;

  /** Make an enumeration type */
  term_ref enum_type(const std::vector<std::string>& args);

  /** Is t an enumeration type */
  bool is_enum_type(term_ref t) const;

  /** Map from names to terms */
  typedef std::map<std::string, term_ref> id_to_term_map;

  /** Make a record type */
  term_ref record_type(const id_to_term_map& fields);

  /** Is t a record type */
  bool is_record_type(term_ref t) const;

  /** Get the type of a field */
  term_ref get_record_type_field_type(term_ref rec_type, std::string field) const;

  /** Get all fields */
  void get_record_type_fields(term_ref rec_type, id_to_term_map& fields) const;

  /** Returns the size of the bitvector type */
  size_t bitvector_type_size(term_ref t) const;

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

  /** Make a term from three children and no payload */
  template<term_op op>
  term_ref mk_term(term_ref child1, term_ref child2, term_ref child3) {
    term_ref children[3] = { child1, child2, child3 };
    return mk_term<op, term_ref*>(alloc::empty_type(), children, children + 3);
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
  term_ref type_of(const term& t);

  /** Get the type of the term if it has been computed */
  term_ref type_of_if_exists(const term& t) const;

  /** Get the type of the term */
  term_ref type_of(term_ref t) {
    if (t.is_null()) return t;
    return type_of(term_of(t));
  }

  /** Get the type of the term if it has been computed */
  term_ref type_of_if_exists(term_ref t) const {
    if (t.is_null()) return t;
    return type_of_if_exists(term_of(t));
  }

  /** Get the base type of the term or type */
  term_ref base_type_of(const term& t);

  /** Get th ebase type of the term or type if it has been computed */
  term_ref base_type_of_if_exists(const term& t) const;

  /** Get the base type of the term or type */
  term_ref base_type_of(term_ref t) {
    if (t.is_null()) return t;
    return base_type_of(term_of(t));
  }

  /** Get the base type of the term or type if it has been computed */
  term_ref base_type_of_if_exists(term_ref t) const {
    if (t.is_null()) return t;
    return base_type_of_if_exists(term_of(t));
  }

  /** Are the types compatible (potentially, looking at base types */
  bool compatible(term_ref t1, term_ref t2);

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

  /** Add a namespace entry (will be removed from prefix when printing. */
  void use_namespace(std::string ns);

  /** Pop the last added namespace */
  void pop_namespace();

  struct subterm_visitor_state {
    const term& t;
    std::set<term_ref> bound_vars;
    subterm_visitor_state(const term& t)
    : t(t) {}
    subterm_visitor_state(const term& t, const std::set<term_ref>& vars)
    : t(t), bound_vars(vars) {}
  };

  /** Matcher for variables */
  struct variable_matcher {
    const term_manager_internal& tm;
    variable_matcher(const term_manager_internal& tm): tm(tm) {}
    bool operator() (const subterm_visitor_state& state) const {
      // Only get the (non-function) variables that are not bound
      if (state.t.op() == VARIABLE && state.bound_vars.count(tm.ref_of(state.t)) == 0) {
        term_ref var_type = tm.type_of_if_exists(state.t);
        assert(!var_type.is_null());
        if (!tm.is_function_type(var_type)) {
          return true;
        }
      }
      return false;
    }
    bool ignore(const term& t) const { return false; }
  };

  /** Return the subterms what return true on m(t) */
  template<typename collection, typename matcher>
  void get_subterms(term_ref t, const matcher& m, collection& out) const;

  /** Returns the variables of the term */
  template<typename collection>
  void get_variables(term_ref t, collection& out) const {
    get_subterms(t, variable_matcher(*this), out);
  }

  /** Returns the default value for the given type */
  term_ref get_default_value(term_ref type);

  /** Map of substitutions */
  typedef boost::unordered_map<term_ref, term_ref, term_ref_hasher> substitution_map;

  /** Return t with subst applied */
  term_ref substitute(term_ref t, substitution_map& subst);

  /** Set a transformer for variable names (set 0 to unset) */
  void set_name_transformer(const utils::name_transformer* transformer);

  /** Get the transformer for variable names (set 0 to unset) */
  const utils::name_transformer* get_name_transformer() const;

  /** Returns the id normalized with resepct to the current namespaces and the name transformer */
  std::string name_normalize(std::string id) const;

  /**
   * Collect the non-used terms, and compact the term database. The relocation
   * map is added to the given map.
   */
  void gc(std::map<expr::term_ref, expr::term_ref>& reloc_map);

  /** Make an abstraction */
  term_ref mk_abstraction(term_op op, const std::vector<term_ref>& vars, term_ref body);

  /** Is this an abstraction */
  bool is_abstraction(const term& t) const;
  bool is_abstraction(term_ref t) const { return is_abstraction(term_of(t)); }

  /** Get body of abstraction */
  term_ref get_abstraction_body(term_ref abstraction) const;

  /** Get abstraction arity */
  size_t get_abstraction_arity(term_ref abstraction) const;

  /** Get i-th abstraction variable */
  term_ref get_abstraction_variable(term_ref abstraction, size_t i) const;

  /** Get all abstraction variables */
  template <typename collection>
  void get_abstraction_variables(const term& t, collection& vars_out) const {
    assert(is_abstraction(t));
    assert(t.size() > 1);
    std::insert_iterator<collection> insert(vars_out, vars_out.end());
    for(size_t i = 0; i < t.size() - 1; ++ i) {
      *insert = t[i];
    }
  }

  template <typename collection>
  void get_abstraction_variables(term_ref t, collection& vars_out) const {
    get_abstraction_variables(term_of(t), vars_out);
  }

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

  // Update the statistic
  d_stat_terms->get_value() = d_memory.size();

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
    SWITCH_TO_TERM(TYPE_STRUCT)
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
    SWITCH_TO_TERM(TERM_MOD)
    SWITCH_TO_TERM(TERM_LEQ)
    SWITCH_TO_TERM(TERM_LT)
    SWITCH_TO_TERM(TERM_GEQ)
    SWITCH_TO_TERM(TERM_GT)
    SWITCH_TO_TERM(TERM_TO_INT)
    SWITCH_TO_TERM(TERM_TO_REAL)
    SWITCH_TO_TERM(TERM_IS_INT)
    SWITCH_TO_TERM(TERM_BV_ADD)
    SWITCH_TO_TERM(TERM_BV_SUB)
    SWITCH_TO_TERM(TERM_BV_MUL)
    SWITCH_TO_TERM(TERM_BV_UDIV)
    SWITCH_TO_TERM(TERM_BV_SDIV)
    SWITCH_TO_TERM(TERM_BV_UREM)
    SWITCH_TO_TERM(TERM_BV_SREM)
    SWITCH_TO_TERM(TERM_BV_SMOD)
    SWITCH_TO_TERM(TERM_BV_ULEQ)
    SWITCH_TO_TERM(TERM_BV_SLEQ)
    SWITCH_TO_TERM(TERM_BV_ULT)
    SWITCH_TO_TERM(TERM_BV_SLT)
    SWITCH_TO_TERM(TERM_BV_UGEQ)
    SWITCH_TO_TERM(TERM_BV_SGEQ)
    SWITCH_TO_TERM(TERM_BV_UGT)
    SWITCH_TO_TERM(TERM_BV_SGT)
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
    SWITCH_TO_TERM(TERM_BV_CONCAT)
    SWITCH_TO_TERM(TERM_FUN_APP)
    SWITCH_TO_TERM(TERM_TUPLE_CONSTRUCT)
  default:
    assert(false);
  }

#undef SWITCH_TO_TERM

  return result;
}

template<typename collection, typename matcher>
void term_manager_internal::get_subterms(term_ref t, const matcher& m, collection& out) const {
  typedef boost::unordered_set<term_ref, term_ref_hasher> visited_set;

  visited_set v;
  std::queue<subterm_visitor_state> queue;

  // If matcher ignores this term, just return
  if (m.ignore(term_of(t))) {
    return;
  }

  // Start with the term itself, then process
  queue.push(subterm_visitor_state(term_of(t)));
  v.insert(t);

  std::insert_iterator<collection> insert(out, out.end());
  while (!queue.empty()) {

    // Process current
    subterm_visitor_state current = queue.front();
    queue.pop();
    if (m(current)) {
      *insert = ref_of(current.t);
    }

    // Collect any bound variables
    std::set<term_ref> bound_vars(current.bound_vars.begin(), current.bound_vars.end());
    if (is_abstraction(current.t)) {
      get_abstraction_variables(current.t, bound_vars);
    }

    // For abstraction only visit the body, otherwise go into all children
    size_t i = is_abstraction(current.t) ? current.t.size() - 1 : 0;
    for (; i < current.t.size(); ++ i) {
      if (v.find(current.t[i]) == v.end()) {
        if (!m.ignore(term_of(current.t[i]))) {
          queue.push(subterm_visitor_state(term_of(current.t[i]), bound_vars));
          v.insert(current.t[i]);
        }
      }
    }
  }
}

}
}
