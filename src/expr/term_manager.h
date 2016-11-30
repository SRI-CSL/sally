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

#include "utils/statistics.h"
#include "expr/term.h"
#include "utils/name_transformer.h"

#include <set>
#include <string>
#include <vector>
#include <boost/unordered_map.hpp>

#include <iosfwd>

namespace sally {
namespace expr {

class gc_participant;
class term_manager_internal;

class term_manager {

  /** Internal term manager implementation */
  term_manager_internal* d_tm;

  friend struct set_tm;

  /** Participants in garbage collection */
  std::set<gc_participant*> d_gc_participants;

  /** Id of the manager */
  size_t d_id;

  /** Total number of managers ever created */
  static size_t s_instances;

  /** Set of all ever used variable names */
  std::set<std::string> d_variable_names;

  /** Ids of temp variables */
  size_t d_tmp_var_id;

public:

  /** Construct them manager */
  term_manager(utils::statistics& stats);

  /** Destruct the manager, and destruct all payloads that the manager owns */
  ~term_manager();

  /** Get the internal term manager */
  term_manager_internal* get_internal() { return d_tm; }

  /** Get the internal term manager */
  const term_manager_internal* get_internal() const { return d_tm; }

  /** Print the term manager information and all the terms to out */
  void to_stream(std::ostream& out) const;

  /** Get the Boolean type */
  term_ref boolean_type() const;

  /** Get the Integer type */
  term_ref integer_type() const;

  /** Get the Real type */
  term_ref real_type() const;

  /** Get the type of bitvectors of given size > 0. */
  term_ref bitvector_type(size_t size);

  /** Make a function type (t1, t2, ..., tn), with ti being types, tn being co-domain */
  term_ref function_type(const std::vector<term_ref>& args);

  /** Get the domain type of a function type */
  term_ref get_function_type_domain(term_ref fun_type, size_t i) const;

  /** Get the co-domain type of a function type */
  term_ref get_function_type_codomain(term_ref fun_type) const;

  /** Make an array type t1 -> t2 */
  term_ref array_type(term_ref index_type, term_ref element_type);

  /** Get the index type of the array type */
  term_ref get_array_type_index(term_ref arr_type) const;

  /** Get the element type of the array type */
  term_ref get_array_type_element(term_ref arr_type) const;

  /** Make a tuple type (t1, t2, ..., tn) with ti being types */
  term_ref tuple_type(const std::vector<term_ref>& args);

  /** Get the k-th element of the tuple type */
  term_ref get_tuple_type_element(term_ref tuple_type, size_t i) const;

  /** Get the size of a bitvector type */
  size_t get_bitvector_type_size(term_ref bv_type) const;

  /** Get the size of a bitvector term */
  size_t get_bitvector_size(term_ref bv_term) const;

  /** Make a term, given children */
  term_ref mk_term(term_op op, term_ref c);

  /** Make a term, given children */
  term_ref mk_term(term_op op, term_ref c1, term_ref c2);

  /** Make a term, given children */
  term_ref mk_term(term_op op, term_ref c1, term_ref c2, term_ref c3);

  /** Make a term, given children */
  term_ref mk_term(term_op op, const std::vector<term_ref>& children);

  /** Make a term, given children */
  term_ref mk_term(term_op op, const term_ref* children_begin, const term_ref* children_end);

  /** Make a term, given children */
  term_ref mk_term(term_op op, const term_ref* children, size_t n) {
    return mk_term(op, children, children + n);
  }

  /** Make a new variable without a name */
  term_ref mk_variable(term_ref type);

  /** Make a new variable */
  term_ref mk_variable(std::string name, term_ref type);

  /** Get the name of this variable */
  std::string get_variable_name(term_ref t) const;

  /** Get the name of this variable */
  std::string get_variable_name(const term& t) const;

  /** Get a fresh variable name (never used before) */
  std::string get_fresh_variable_name();

  /** Reset the fresh variables counter */
  void reset_fresh_variables();

  /** Make a new boolean constant */
  term_ref mk_boolean_constant(bool value);

  /** Returns the boolan constant value */
  bool get_boolean_constant(const term& t) const;

  /** Returns the default value for the given type */
  term_ref get_default_value(term_ref type) const;

  /** Returns the conjuncts of the formula */
  void get_conjuncts(term_ref f, std::set<term_ref>& out);

  /** Returns the conjuncts of the formula */
  void get_conjuncts(term_ref f, std::vector<term_ref>& out);

  /** Returns the conjuncts of the formula */
  void get_disjuncts(term_ref f, std::set<term_ref>& out);

  /** Make a negation (simplifies a bit) */
  term_ref mk_not(term_ref f1);

  /** Make a conjunction (simplifies a bit). */
  term_ref mk_and(term_ref f1, term_ref f2);

  /** Make a disjunction (simplifies a bit). */
  term_ref mk_or(term_ref f1, term_ref f2);

  /** Name a disjunction (simplifies a bit). */
  term_ref mk_or(term_ref f);

  /** Make a conjunction. If no children => true. One child => child. */
  term_ref mk_and(const std::vector<term_ref>& conjuncts);

  /** Make a conjunction. If no children => true. One child => child. */
  term_ref mk_and(const std::set<term_ref>& conjuncts);

  /** Make a disjunction. If no children => false. One child => child. */
  term_ref mk_or(const std::vector<term_ref>& disjuncts);

  /** Make a new rational constant */
  term_ref mk_rational_constant(const rational& value);

  /** Returns the rational constant value */
  rational get_rational_constant(const term& t) const;

  /** Make a new bitvector constant */
  term_ref mk_bitvector_constant(const bitvector& bv);

  /** Return the bitvector constant value */
  bitvector get_bitvector_constant(const term& t) const;

  /** Make a new bitvector extract operator */
  term_ref mk_bitvector_extract(term_ref t, const bitvector_extract& extract);

  /** Make a new bitvector sgn extend */
  term_ref mk_bitvector_sgn_extend(term_ref t, const bitvector_sgn_extend& extend);

  /** Get the extract of the extract term */
  bitvector_extract get_bitvector_extract(const term& t) const;

  /** Get the sgn extend of the extend term */
  bitvector_sgn_extend get_bitvector_sgn_extend(const term& t) const;

  /** Make an array read term */
  term_ref mk_array_read(term_ref a, term_ref index);

  /** Get array from the array read */
  term_ref get_array_read_array(term_ref aread) const;

  /** Get the index from the array read */
  term_ref get_array_read_index(term_ref aread) const;

  /** Make an array write term */
  term_ref mk_array_write(term_ref a, term_ref index, term_ref element);

  /** Get the array from the array write */
  term_ref get_array_write_array(term_ref awrite) const;

  /** Get the index from the array write */
  term_ref get_array_write_index(term_ref awrite) const;

  /** Get the element from the array write */
  term_ref get_array_write_element(term_ref awrite) const;

  /** Construct tuple */
  term_ref mk_tuple(const std::vector<term_ref>& elements) const;

  /** Make a tuple acess term */
  term_ref mk_tuple_access(term_ref t, size_t i);

  /** Get the tuple access base tuple */
  term_ref get_tuple_access_tuple(term_ref taccess) const;

  /** Get the tuple access index */
  size_t get_tuple_access_index(term_ref taccess) const;

  /** Make a new tuple write term */
  term_ref mk_tuple_write(term_ref t, size_t i, term_ref e);

  /** Get the tuple write base tuple */
  term_ref get_tuple_write_tuple(term_ref twrite) const;

  /** Get the tuple write index */
  size_t get_tuple_write_index(term_ref twrite) const;

  /** Get the tuple write written element */
  term_ref get_tuple_write_element(term_ref twrite) const;

  /** Make function application */
  term_ref mk_function_application(term_ref fun, const std::vector<term_ref>& args);

  /** Make a new string constant */
  term_ref mk_string_constant(std::string value);

  /** Returns the string constant value */
  std::string get_string_constant(const term& t) const;

  /** Make a new struct type */
  term_ref mk_struct_type(const std::vector<std::string>& names, const std::vector<term_ref>& types);

  /** Get the size of the type */
  size_t get_struct_type_size(const term& t) const;

  /** Get the id of i-th struct element */
  std::string get_struct_type_field_id(const term& t, size_t i) const;

  /** Get the type of the struct element */
  term_ref get_struct_type_field_type(const term& t, size_t i) const;

  /** Get the field of a struct variable */
  size_t get_struct_size(const term& t) const;

  /** Get the field of a struct variable */
  term_ref get_struct_field(const term& t, size_t i) const;

  /**
   * Helper for constructing abstraction variables and creating lambdas and
   * quantified terms. One can create variable, and the only way to remove
   * variables from the helper is to create a term.
   */
  class abstraction_helper {

    /** The term manager */
    term_manager& d_term_manager;

    /** Variables */
    std::vector<term_ref> d_variables;

    /** Variable names */
    std::vector<std::string> d_names;

    /** Make the abstraction, taking n top variables */
    term_ref mk_abstraction(term_op, size_t n, term_ref body);

  public:

    /** Create an abstraction helper */
    abstraction_helper(term_manager& term_manager);

    /** Check that all variables have been used */
    ~abstraction_helper();

    /** Create new bound variable */
    term_ref new_bound_variable(term_ref type);

    /** Create new bound variable with a name */
    term_ref new_bound_variable(std::string name, term_ref type);

    /** Create a lambda term (pops all variables) */
    term_ref mk_lambda(term_ref body);

    /** Create an exist quantifier (pops n variables) */
    term_ref mk_exists(term_ref body, size_t n);

    /** Create a forall quantifier (pops n variables) */
    term_ref mk_forall(term_ref body, size_t n);

    /** Create a predicate sub-type (pops the one variable) */
    term_ref mk_predicate_subtype(term_ref body);
  };

  /** Get the index of an abstraction variable */
  size_t get_bound_variable_idx(term_ref x) const;

  /** Get the arity of the abstraction */
  size_t get_abstraction_arity(term_ref abstraction) const;
  size_t get_lambda_arity(term_ref lambda) const;
  size_t get_quantifier_arity(term_ref quantifier) const;

  /** The the body of the abstraction */
  term_ref get_abstraction_body(term_ref abstraction) const;
  term_ref get_lambda_body(term_ref lambda) const;
  term_ref get_quantifier_body(term_ref quantifier) const;
  term_ref get_predicate_subtype_body(term_ref pred_type) const;

  /** Get the i-th bound variable of the term (lambda, exists, forall) */
  term_ref get_abstraction_variable(term_ref abstraction, size_t i) const;
  term_ref get_lambda_variable(term_ref lambda, size_t i) const;
  term_ref get_quantifier_variable(term_ref quantifier, size_t i) const;
  term_ref get_predicate_subtype_variable(term_ref pred_type) const;

  /** Get all the variables of the lambda, in order */
  void get_abstraction_variables(term_ref lambda, std::vector<term_ref>& vars_out) const;
  void get_lambda_variables(term_ref lambda, std::vector<term_ref>& vars_out) const;
  void get_quantifier_variables(term_ref lambda, std::vector<term_ref>& vars_out) const;

  /** Get all fields of a struct variable */
  void get_struct_fields(const term& t, std::vector<term_ref>& out) const;

  /** Get a reference for the term */
  term_ref ref_of(const term& term) const;

  /** Get a term of the reference */
  const term& term_of(term_ref ref) const;

  /** Get the number of children this term has. */
  size_t term_size(const term& t) const;

  /** First child */
  const term_ref* term_begin(const term& t) const;

  /** End of children (one past) */
  const term_ref* term_end(const term& t) const;

  /** Get the type of the term */
  term_ref type_of(const term& t) const;

  /** Get the type of the term */
  term_ref type_of(term_ref t) const {
    return type_of(term_of(t));
  }

  /** Check if t1 is a subtype of t2 (say integer and real) */
  bool is_subtype_of(term_ref t1, term_ref t2) const;

  /** Get the TCC of the term */
  term_ref tcc_of(const term& t) const;

  /** Get the TCC of the term */
  term_ref tcc_of(const term_ref& t) const {
    return tcc_of(term_of(t));
  }

  /** Get the id of the term */
  size_t id_of(term_ref ref) const;

  /** Get the hash of the term */
  size_t hash_of(term_ref ref) const {
    if (ref.is_null()) return 0;
    return term_of(ref).hash();
  }

  /** Get the variables of the term */
  void get_variables(term_ref ref, std::vector<term_ref>& out) const;

  /** Get the variables of the term */
  void get_variables(term_ref ref, std::set<term_ref>& out) const;

  /** Get number of variables that the term has */
  size_t get_variables_count(term_ref ref) const;

  /** Get the bound variables of the term, in order from outermost scope to innermost scope */
  void get_bound_variables(term_ref ref, std::vector<term_ref>& out) const;

  /** Get the variables of the term */
  void get_bound_variables(term_ref ref, std::set<term_ref>& out) const;

  /** Get number of variables that the term has */
  size_t get_bound_variables_count(term_ref ref) const;

  /** Get the subterms of the term */
  void get_subterms(term_ref ref, std::vector<term_ref>& out) const;

  /** Get the string representation of the term */
  std::string to_string(term_ref ref) const;

  /** Add a namespace entry (will be removed from prefix when printing. */
  void use_namespace(std::string ns);

  /** Pop the last added namespace */
  void pop_namespace();

  /** Set a transformer for variable names (set 0 to unset) */
  void set_name_transformer(const utils::name_transformer* transformer);

  /** Given a name, reduce it using the namespaces and the name transformer */
  std::string name_normalize(std::string name) const;

  /** The substitution map */
  typedef boost::unordered_map<term_ref, term_ref, term_ref_hasher> substitution_map;

  /** Replaces terms from t that appear in the map. */
  term_ref substitute(term_ref t, const substitution_map& subst);

  /** Replaces terms from t that appear in the map. */
  term_ref substitute_and_cache(term_ref t, substitution_map& subst);

  /** Get the current name transformer */
  const utils::name_transformer* get_name_transformer() const;

  /** Perform garbage collection */
  void gc();

  /** Register for garbage collection */
  void gc_register(gc_participant* o);

  /** Unregister from garbage collection */
  void gc_deregister(gc_participant* o);

  /** Id of this manager */
  size_t id() const;
};

inline
std::ostream& operator << (std::ostream& out, const term_manager& tm) {
  tm.to_stream(out);
  return out;
}

/** IO modifier to set the term manager */
struct set_tm {
  term_manager& d_tm;
  set_tm(term_manager& tm): d_tm(tm) {}
};

/** IO manipulator to set the term manager on the stream */
std::ostream& operator << (std::ostream& out, const set_tm& stm);

/** IO modifier to set the output language */
struct set_output_language {
  output::language d_lang;
  set_output_language(output::language lang): d_lang(lang) {}
};

/** IO manipulator to set the output language on the stream */
std::ostream& operator << (std::ostream& out, const set_output_language& stm);

}
}
