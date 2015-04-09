/*
 * term_manager.cpp
 *
 *  Created on: Nov 17, 2014
 *      Author: dejan
 */

#include "expr/term_manager.h"
#include "expr/term_manager_internal.h"
#include "utils/trace.h"
#include "expr/gc_participant.h"

#include <iostream>
#include <sstream>

namespace sally {
namespace expr {

term_manager::term_manager(bool typecheck)
: d_tm(new term_manager_internal(typecheck))
, d_eq_rewrite(false)
{
}

term_manager::~term_manager() {
  delete d_tm;
}

void term_manager::to_stream(std::ostream& out) const {
  d_tm->to_stream(out);
}

term_ref term_manager::boolean_type() const {
  return d_tm->boolean_type();
}

term_ref term_manager::integer_type() const {
  return d_tm->integer_type();
}

term_ref term_manager::real_type() const {
  return d_tm->real_type();
}

term_ref term_manager::bitvector_type(size_t size) {
  return d_tm->bitvector_type(size);
}

size_t term_manager::get_bitvector_type_size(term_ref t_ref) const {
  const term& t = d_tm->term_of(t_ref);
  assert(t.op() == TYPE_BITVECTOR);
  return d_tm->payload_of<size_t>(t);
}

size_t term_manager::get_bitvector_size(term_ref t_ref) const {
  term_ref t_type = type_of(t_ref);
  return get_bitvector_type_size(t_type);
}

term_ref term_manager::mk_term(term_op op, const std::vector<term_ref>& children) {
  if (children.size() == 2) {
    return mk_term(op, children[0], children[1]);
  } else {
    return d_tm->mk_term(op, children.begin(), children.end());
  }
}

term_ref term_manager::mk_term(term_op op, const term_ref* children_begin, const term_ref* children_end) {
  if (children_end - children_begin == 2) {
    return mk_term(op, *children_begin, *(children_begin + 1));
  } else {
    return d_tm->mk_term(op, children_begin, children_end);
  }
}

term_ref term_manager::mk_term(term_op op, term_ref c) {
  term_ref children[1] = { c };
  return d_tm->mk_term(op, children, children + 1);
}

void term_manager::set_eq_rewrite(bool flag) {
  d_eq_rewrite = flag;
}

term_ref term_manager::mk_term(term_op op, term_ref c1, term_ref c2) {
  if (d_eq_rewrite && op == expr::TERM_EQ && d_tm->is_subtype_of(type_of(c1), real_type())) {
    term_ref leq = d_tm->mk_term<expr::TERM_LEQ>(c1, c2);
    term_ref geq = d_tm->mk_term<expr::TERM_GEQ>(c1, c2);
    return d_tm->mk_term<expr::TERM_AND>(leq, geq);
  } else {
    term_ref children[2] = { c1 , c2 };
    return d_tm->mk_term(op, children, children + 2);
  }
}

term_ref term_manager::mk_term(term_op op, term_ref c1, term_ref c2, term_ref c3) {
  term_ref children[3] = { c1 , c2, c3 };
  return d_tm->mk_term(op, children, children + 3);
}

term_ref term_manager::mk_variable(term_ref type) {
  static size_t id = 0;
  std::stringstream ss;
  ss << "_" << (id ++);
  return mk_variable(ss.str(), type);
}

term_ref term_manager::mk_variable(std::string name, term_ref type) {
  if (term_of(type).op() == TYPE_STRUCT) {
    // Size of the struct
    size_t fields_count = get_struct_type_size(term_of(type));
    // For a struct type, we create the variable, with with sub-variables
    std::vector<term_ref> children;
    // First child is the type itself
    children.push_back(type);
    // Other children are the field variables
    for (size_t field_i = 0; field_i < fields_count; ++ field_i) {
      // Name of the field
      std::string field_id = get_struct_type_field_id(term_of(type), field_i);
      // Type of the field
      term_ref field_type = get_struct_type_field_type(term_of(type), field_i);
      // Add the variable
      children.push_back(d_tm->mk_term<VARIABLE>(name + "." + field_id, field_type));
    }
    // Make the struct variable
    return d_tm->mk_term<VARIABLE>(name, children.begin(), children.end());
  } else {
    // If this is not a struct type, we just create the variable
    return d_tm->mk_term<VARIABLE>(name, type);
  }
}

std::string term_manager::get_variable_name(const term& t) const {
  assert(t.op() == VARIABLE);
  std::string name = d_tm->payload_of<std::string>(t);
  return d_tm->name_normalize(name);
}

std::string term_manager::name_normalize(std::string name) const {
  return d_tm->name_normalize(name);
}

term_ref term_manager::mk_boolean_constant(bool value) {
  return d_tm->mk_term<CONST_BOOL>(value);
}

term_ref term_manager::mk_integer_constant(const integer& value) {
  return d_tm->mk_term<CONST_INTEGER>(value);
}

term_ref term_manager::mk_rational_constant(const rational& value) {
  return d_tm->mk_term<CONST_RATIONAL>(value);
}

term_ref term_manager::mk_bitvector_constant(const bitvector& value) {
  return d_tm->mk_term<CONST_BITVECTOR>(value);
}

term_ref term_manager::mk_bitvector_extract(term_ref t, const bitvector_extract& extract) {
  return d_tm->mk_term<expr::TERM_BV_EXTRACT>(extract, t);
}

term_ref term_manager::mk_string_constant(std::string value) {
  return d_tm->mk_term<CONST_STRING>(value);
}

bool term_manager::get_boolean_constant(const term& t) const {
  assert(t.op() == CONST_BOOL);
  return d_tm->payload_of<bool>(t);
}

integer term_manager::get_integer_constant(const term& t) const {
  assert(t.op() == CONST_INTEGER);
  return d_tm->payload_of<integer>(t);
}

rational term_manager::get_rational_constant(const term& t) const {
  assert(t.op() == CONST_RATIONAL);
  return d_tm->payload_of<rational>(t);
}

bitvector term_manager::get_bitvector_constant(const term& t) const {
  assert(t.op() == CONST_BITVECTOR);
  return d_tm->payload_of<bitvector>(t);
}

bitvector_extract term_manager::get_bitvector_extract(const term& t) const {
  assert(t.op() == TERM_BV_EXTRACT);
  return d_tm->payload_of<bitvector_extract>(t);
}

std::string term_manager::get_string_constant(const term& t) const {
  assert(t.op() == CONST_STRING);
  return d_tm->payload_of<std::string>(t);
}

term_ref term_manager::mk_struct_type(const std::vector<std::string>& names, const std::vector<term_ref>& types) {

  std::vector<term_ref> type_argumens;

  for (size_t i = 0; i < names.size(); ++ i) {
    type_argumens.push_back(mk_string_constant(names[i]));
    type_argumens.push_back(types[i]);
  }

  return mk_term(TYPE_STRUCT, type_argumens);
}

size_t term_manager::get_struct_type_size(const term& t) const {
  assert(t.op() == TYPE_STRUCT);
  return t.size() / 2;
}

std::string term_manager::get_struct_type_field_id(const term& t, size_t i) const {
  assert(t.op() == TYPE_STRUCT);
  const term& id_term = term_of(t[2*i]);
  return get_string_constant(id_term);
}

term_ref term_manager::get_struct_type_field_type(const term& t, size_t i) const {
  assert(t.op() == TYPE_STRUCT);
  return t[2*i + 1];
}

size_t term_manager::get_struct_size(const term& t) const {
  assert(t.op() == VARIABLE);
  return t.size() - 1;
}

term_ref term_manager::get_struct_field(const term& t, size_t i) const {
  assert(t.op() == VARIABLE);
  assert(i + 1 < t.size());
  return t[i + 1];
}

term_ref term_manager::ref_of(const term& term) const {
  return d_tm->ref_of(term);
}

const term& term_manager::term_of(term_ref ref) const {
  return d_tm->term_of(ref);
}

size_t term_manager::term_size(const term& t) const {
  return d_tm->term_size(t);
}

const term_ref* term_manager::term_begin(const term& t) const {
  return d_tm->term_begin(t);
}

const term_ref* term_manager::term_end(const term& t) const {
  return d_tm->term_end(t);
}

term_ref term_manager::type_of(const term& t) const {
  return d_tm->type_of(t);
}

term_ref term_manager::tcc_of(const term& t) const {
  return d_tm->tcc_of(t);
}

size_t term_manager::id_of(term_ref ref) const {
  return d_tm->id_of(ref);
}

std::string term_manager::to_string(term_ref ref) const {
  return d_tm->to_string(ref);
}

void term_manager::use_namespace(std::string ns) {
  d_tm->use_namespace(ns);
}

void term_manager::pop_namespace() {
  d_tm->pop_namespace();
}

struct variable_matcher {
  bool operator() (const term& t) const {
    return t.op() == VARIABLE;
  }
};

void term_manager::get_variables(term_ref ref, std::vector<term_ref>& out) const {
  d_tm->get_subterms(ref, variable_matcher(), out);
}

void term_manager::get_variables(term_ref ref, std::set<term_ref>& out) const {
  d_tm->get_subterms(ref, variable_matcher(), out);
}

term_ref term_manager::substitute(term_ref t, const substitution_map& subst) {
  substitution_map subst_copy(subst);
  return d_tm->substitute(t, subst_copy);
}

term_ref term_manager::mk_and(const std::vector<term_ref>& conjuncts) {
  if (conjuncts.size() == 0) {
    return mk_boolean_constant(true);
  }
  if (conjuncts.size() == 1) {
    return *conjuncts.begin();
  }
  return d_tm->mk_term<TERM_AND>(conjuncts.begin(), conjuncts.end());
}

term_ref term_manager::mk_and(const std::set<term_ref>& conjuncts) {
  if (conjuncts.size() == 0) {
    return mk_boolean_constant(true);
  }
  if (conjuncts.size() == 1) {
    return *conjuncts.begin();
  }
  return d_tm->mk_term<TERM_AND>(conjuncts.begin(), conjuncts.end());
}

term_ref term_manager::mk_or(const std::vector<term_ref>& disjuncts) {
  if (disjuncts.size() == 0) {
    return mk_boolean_constant(false);
  }
  if (disjuncts.size() == 1) {
    return disjuncts[0];
  }
  return d_tm->mk_term<TERM_OR>(disjuncts.begin(), disjuncts.end());
}

bool term_manager::is_subtype_of(term_ref t1, term_ref t2) const {
  return d_tm->is_subtype_of(t1, t2);
}

bool term_manager::equal_constants(term_ref t1, term_ref t2) const {
  if (is_subtype_of(type_of(t1), real_type())) {
    return rational(*this, t1) == rational(*this, t2);
  }
  return t1 == t2;
}

void term_manager::set_name_transformer(const utils::name_transformer* transformer) {
  d_tm->set_name_transformer(transformer);
}

const utils::name_transformer* term_manager::get_name_transformer() const {
  return d_tm->get_name_transformer();
}

term_ref term_manager::get_default_value(term_ref type) const {
  return d_tm->get_default_value(type);
}

std::ostream& operator << (std::ostream& out, const set_tm& stm) {
  output::set_term_manager(out, stm.d_tm);
  return out;
}

std::ostream& operator << (std::ostream& out, const set_output_language& stm) {
  output::set_output_language(out, stm.d_lang);
  return out;
}

void term_manager::gc() {
  TRACE("gc") << "term_manager::gc(): start" << std::endl;

  std::set<gc_participant*>::iterator it = d_gc_participants.begin();
  for (; it != d_gc_participants.end(); ++ it) {

  }


  TRACE("gc") << "term_manager::gc(): done" << std::endl;
}

void term_manager::gc_register(gc_participant* o) {
  assert(d_gc_participants.find(o) == d_gc_participants.end());
  d_gc_participants.insert(o);
}

void term_manager::gc_deregister(gc_participant* o) {
  assert(d_gc_participants.find(o) != d_gc_participants.end());
  d_gc_participants.erase(o);
}

}
}
