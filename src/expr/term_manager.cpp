/*
 * term_manager.cpp
 *
 *  Created on: Nov 17, 2014
 *      Author: dejan
 */

#include "expr/term_manager.h"
#include "expr/term_manager_internal.h"

using namespace sal2;
using namespace expr;

term_manager::term_manager(bool typecheck)
: d_tm(new term_manager_internal(typecheck))
{
}

term_manager::~term_manager() {
  delete d_tm;
}

void term_manager::to_stream(std::ostream& out) const {
  d_tm->to_stream(out);
}

term_ref term_manager::booleanType() const {
  return d_tm->booleanType();
}

term_ref term_manager::integerType() const {
  return d_tm->integerType();
}

term_ref term_manager::realType() const {
  return d_tm->realType();
}

term_ref term_manager::mk_term(term_op op, const std::vector<term_ref>& children) {
  return d_tm->mk_term(op, children.begin(), children.end());
}

term_ref term_manager::mk_term(term_op op, const term_ref* children_begin, const term_ref* children_end) {
  return d_tm->mk_term(op, children_begin, children_end);
}

term_ref term_manager::mk_term(term_op op, term_ref c) {
  term_ref children[1] = { c };
  return d_tm->mk_term(op, children, children + 1);
}

term_ref term_manager::mk_term(term_op op, term_ref c1, term_ref c2) {
  term_ref children[2] = { c1 , c2 };
  return d_tm->mk_term(op, children, children + 2);
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
  return d_tm->namespace_normalize(name);
}

term_ref term_manager::mk_boolean_constant(bool value) {
  return d_tm->mk_term<CONST_BOOL>(value);
}

term_ref term_manager::mk_rational_constant(const rational& value) {\
  return d_tm->mk_term<CONST_RATIONAL>(value);
}

term_ref term_manager::mk_string_constant(std::string value) {
  return d_tm->mk_term<CONST_STRING>(value);
}

bool term_manager::get_boolean_constant(const term& t) const {
  assert(t.op() == CONST_BOOL);
  return d_tm->payload_of<bool>(t);
}

rational term_manager::get_rational_constant(const term& t) const {
  assert(t.op() == CONST_RATIONAL);
  return d_tm->payload_of<rational>(t);
}

std::string term_manager::get_string_constant(const term& t) const {
  assert(t.op() == CONST_STRING);
  return d_tm->payload_of<std::string>(t);
}

term_ref term_manager::mk_struct(const std::vector<std::string>& names, const std::vector<term_ref>& types) {

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
