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

#include "expr/term_manager.h"
#include "expr/term_manager_internal.h"
#include "utils/trace.h"
#include "utils/string.h"
#include "expr/gc_participant.h"
#include "expr/gc_relocator.h"

#include <string>
#include <iostream>
#include <sstream>

namespace sally {
namespace expr {

size_t term_manager::s_instances = 0;

term_manager::term_manager(utils::statistics& stats)
: d_tm(new term_manager_internal(stats))
, d_id(s_instances ++)
, d_tmp_var_id(0)
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
  term_ref result;
  if (children.size() == 2) {
    result = mk_term(op, children[0], children[1]);
  } else if (children.size() == 1 && (op == term_op::TERM_AND || op == term_op::TERM_OR)) {
    result = children[0];
  } else {
    result = d_tm->mk_term(op, children.begin(), children.end());
  }
  d_tm->typecheck(result);
  return result;
}

term_ref term_manager::mk_term(term_op op, const term_ref* children_begin, const term_ref* children_end) {
  term_ref result;
  if (children_end - children_begin == 2) {
    result = mk_term(op, *children_begin, *(children_begin + 1));
  } else {
    result = d_tm->mk_term(op, children_begin, children_end);
  }
  d_tm->typecheck(result);
  return result;
}

term_ref term_manager::mk_term(term_op op, term_ref c) {
  term_ref children[1] = { c };
  term_ref result = d_tm->mk_term(op, children, children + 1);
  d_tm->typecheck(result);
  return result;
}

term_ref term_manager::mk_term(term_op op, term_ref c1, term_ref c2) {
  term_ref children[2] = { c1 , c2 };
  term_ref result = d_tm->mk_term(op, children, children + 2);
  d_tm->typecheck(result);
  return result;
}

term_ref term_manager::mk_term(term_op op, term_ref c1, term_ref c2, term_ref c3) {
  term_ref children[3] = { c1 , c2, c3 };
  term_ref result = d_tm->mk_term(op, children, children + 3);
  d_tm->typecheck(result);
  return result;
}

term_ref term_manager::mk_variable(term_ref type) {
  static size_t id = 0;
  std::stringstream ss;
  ss << "_" << (id ++);
  d_variable_names.insert(ss.str());
  term_ref result = mk_variable(ss.str(), type);
  d_tm->typecheck(result);
  return result;
}

term_ref term_manager::mk_variable(std::string name, term_ref type) {
  d_variable_names.insert(name);
  term_ref result;
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
    result = d_tm->mk_term<VARIABLE>(name, children.begin(), children.end());
  } else {
    // If this is not a struct type, we just create the variable
    result = d_tm->mk_term<VARIABLE>(name, type);
  }
  d_tm->typecheck(result);
  return result;
}

std::string term_manager::get_fresh_variable_name() {
  for (;;) {
    std::stringstream ss;
    ss << "l" << (d_tmp_var_id ++);
    std::string name = ss.str();
    if (d_variable_names.count(name) == 0) {
      return name;
    }
  }
  return "never_here";
}

void term_manager::reset_fresh_variables() {
  d_tmp_var_id = 0;
}

std::string term_manager::get_variable_name(term_ref t_ref) const {
  const term& t = d_tm->term_of(t_ref);
  return get_variable_name(t);
}

std::string term_manager::get_variable_name(const term& t) const {
  assert(t.op() == VARIABLE);
  std::string name(d_tm->payload_of<utils::string>(t).c_str());
  return d_tm->name_normalize(name);
}

std::string term_manager::name_normalize(std::string name) const {
  return d_tm->name_normalize(name);
}

term_ref term_manager::mk_boolean_constant(bool value) {
  return d_tm->mk_term<CONST_BOOL>(value);
}

term_ref term_manager::mk_rational_constant(const rational& value) {
  return d_tm->mk_term<CONST_RATIONAL>(value);
}

term_ref term_manager::mk_bitvector_constant(const bitvector& value) {
  return d_tm->mk_term<CONST_BITVECTOR>(value);
}

term_ref term_manager::mk_bitvector_extract(term_ref t, const bitvector_extract& extract) {
  term_ref result = d_tm->mk_term<TERM_BV_EXTRACT>(extract, t);
  d_tm->typecheck(result);
  return result;
}

term_ref term_manager::mk_bitvector_sgn_extend(term_ref t, const bitvector_sgn_extend& extend) {
  term_ref result = d_tm->mk_term<TERM_BV_SGN_EXTEND>(extend, t);
  d_tm->typecheck(result);
  return result;
}

term_ref term_manager::mk_array_read(term_ref a, term_ref index) {
  term_ref result = d_tm->mk_term<TERM_ARRAY_READ>(a, index);
  d_tm->typecheck(result);
  return result;
}

term_ref term_manager::get_array_read_array(term_ref aread) const {
  const term& t = term_of(aread);
  assert(t.op() == TERM_ARRAY_READ);
  return t[0];
}

term_ref term_manager::get_array_read_index(term_ref aread) const {
  const term& t = term_of(aread);
  assert(t.op() == TERM_ARRAY_READ);
  return t[1];
}

term_ref term_manager::mk_array_write(term_ref a, term_ref index, term_ref element) {
  term_ref result = d_tm->mk_term<TERM_ARRAY_WRITE>(a, index, element);
  d_tm->typecheck(result);
  return result;
}

term_ref term_manager::get_array_write_array(term_ref awrite) const {
  const term& t = term_of(awrite);
  assert(t.op() == TERM_ARRAY_WRITE);
  return t[0];
}

term_ref term_manager::get_array_write_index(term_ref awrite) const {
  const term& t = term_of(awrite);
  assert(t.op() == TERM_ARRAY_WRITE);
  return t[1];
}

term_ref term_manager::get_array_write_element(term_ref awrite) const {
  const term& t = term_of(awrite);
  assert(t.op() == TERM_ARRAY_WRITE);
  return t[2];
}

term_ref term_manager::mk_tuple(const std::vector<term_ref>& elements) {
  term_ref result = d_tm->mk_term<TERM_TUPLE_CONSTRUCT>(elements.begin(), elements.end());
  d_tm->typecheck(result);
  return result;
}

term_ref term_manager::mk_tuple_read(term_ref t, size_t i) {
  term_ref result = d_tm->mk_term<TERM_TUPLE_READ>(i, t);
  d_tm->typecheck(result);
  return result;
}

term_ref term_manager::get_tuple_read_tuple(term_ref taccess) const {
  const term& t = term_of(taccess);
  assert(t.op() == TERM_TUPLE_READ);
  return t[0];
}

size_t term_manager::get_tuple_read_index(term_ref taccess) const {
  const term& t = term_of(taccess);
  assert(t.op() == TERM_TUPLE_READ);
  return d_tm->payload_of<size_t>(t);
}

term_ref term_manager::mk_tuple_write(term_ref t, size_t i, term_ref e) {
  term_ref children[2] = { t, e };
  term_ref result = d_tm->mk_term<TERM_TUPLE_WRITE>(i, children, children + 2);
  d_tm->typecheck(result);
  return result;
}

term_ref term_manager::get_tuple_write_tuple(term_ref twrite) const {
  const term& t = term_of(twrite);
  assert(t.op() == TERM_TUPLE_WRITE);
  return t[0];
}

size_t term_manager::get_tuple_write_index(term_ref twrite) const {
  const term& t = term_of(twrite);
  assert(t.op() == TERM_TUPLE_WRITE);
  return d_tm->payload_of<size_t>(t);
}

term_ref term_manager::get_tuple_write_element(term_ref twrite) const {
  const term& t = term_of(twrite);
  assert(t.op() == TERM_TUPLE_WRITE);
  return t[1];
}

term_ref term_manager::mk_record(const id_to_term_map& elements) {
  std::vector<term_ref> children;
  id_to_term_map::const_iterator it = elements.begin(), end = elements.end();
  for (; it != end; ++ it) {
    children.push_back(mk_string_constant(it->first));
    children.push_back(it->second);
  }
  term_ref result = d_tm->mk_term<TERM_RECORD_CONSTRUCT>(children.begin(), children.end());
  d_tm->typecheck(result);
  return result;
}

term_ref term_manager::mk_record_read(term_ref t, term_ref field_id) {
  term_ref result = d_tm->mk_term<TERM_RECORD_READ>(t, field_id);
  d_tm->typecheck(result);
  return result;
}

term_ref term_manager::get_record_read_record(term_ref rec_read) const {
  const term& t = term_of(rec_read);
  assert(t.op() == TERM_RECORD_READ);
  return t[0];
}

term_ref term_manager::get_record_read_field(term_ref rec_read) const {
  const term& t = term_of(rec_read);
  assert(t.op() == TERM_RECORD_READ);
  return t[1];
}

term_ref term_manager::mk_record_write(term_ref t, term_ref field_id, term_ref value) {
  term_ref children[3] = { t, field_id, value };
  term_ref result = d_tm->mk_term<TERM_RECORD_WRITE>(children, children + 3);
  d_tm->typecheck(result);
  return result;
}

term_ref term_manager::get_record_write_record(term_ref twrite) const {
  const term& t = term_of(twrite);
  assert(t.op() == TERM_RECORD_WRITE);
  return t[0];
}

term_ref term_manager::get_record_write_field(term_ref twrite) const {
  const term& t = term_of(twrite);
  assert(t.op() == TERM_RECORD_WRITE);
  return t[1];
}

term_ref term_manager::get_record_write_element(term_ref twrite) const {
  const term& t = term_of(twrite);
  assert(t.op() == TERM_RECORD_WRITE);
  return t[2];
}


term_ref term_manager::mk_function_application(term_ref fun, const std::vector<term_ref>& args) {
  std::vector<term_ref> children;
  children.push_back(fun);
  children.insert(children.end(), args.begin(), args.end());
  term_ref result = d_tm->mk_term<TERM_FUN_APP>(children.begin(), children.end());
  d_tm->typecheck(result);
  return result;
}

term_ref term_manager::mk_enum_constant(std::string value, term_ref type) {
  const term& type_term = term_of(type);
  assert(type_term.op() == TYPE_ENUM);
  for (size_t i = 0; i < type_term.size(); ++ i) {
    const term& id = term_of(type_term[i]);
    if (get_string_constant(id) == value) {
      return mk_enum_constant(i, type);
    }
  }
  assert(false);
  return term_ref();
}

term_ref term_manager::mk_enum_constant(size_t value, term_ref type) {
  term_ref result = d_tm->mk_term<CONST_ENUM>(value, type);
  d_tm->typecheck(result);
  return result;
}

size_t term_manager::get_enum_constant_value(term_ref t) const {
  assert(term_of(t).op() == CONST_ENUM);
  return d_tm->payload_of<size_t>(t);
}

std::string term_manager::get_enum_constant_id(term_ref t) const {
  const term& t_term = term_of(t);
  assert(t_term.op() == CONST_ENUM);
  const term& type_term = term_of(t_term[0]);
  size_t i = d_tm->payload_of<size_t>(t_term);
  const term& string_term = term_of(type_term[i]);
  return get_string_constant(string_term);
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

bitvector term_manager::get_bitvector_constant(const term& t) const {
  assert(t.op() == CONST_BITVECTOR);
  return d_tm->payload_of<bitvector>(t);
}

bitvector_extract term_manager::get_bitvector_extract(const term& t) const {
  assert(t.op() == TERM_BV_EXTRACT);
  return d_tm->payload_of<bitvector_extract>(t);
}

bitvector_sgn_extend term_manager::get_bitvector_sgn_extend(const term& t) const {
  assert(t.op() == TERM_BV_SGN_EXTEND);
  return d_tm->payload_of<bitvector_sgn_extend>(t);
}

std::string term_manager::get_string_constant(const term& t) const {
  assert(t.op() == CONST_STRING);
  return d_tm->payload_of<utils::string>(t).c_str();
}

term_ref term_manager::function_type(const std::vector<term_ref>& args) {
  return d_tm->function_type(args);
}

term_ref term_manager::get_function_type_domain(term_ref fun_type, size_t i) const {
  return d_tm->get_function_type_domain(fun_type, i);
}

term_ref term_manager::get_function_type_codomain(term_ref fun_type) const {
  return d_tm->get_function_type_codomain(fun_type);
}

term_ref term_manager::array_type(term_ref index_type, term_ref element_type) {
  return d_tm->array_type(index_type, element_type);
}

term_ref term_manager::get_array_type_index(term_ref arr_type) const {
  return d_tm->get_array_type_index(arr_type);
}

term_ref term_manager::get_array_type_element(term_ref arr_type) const {
  return d_tm->get_array_type_element(arr_type);
}

term_ref term_manager::tuple_type(const std::vector<term_ref>& args) {
  return d_tm->tuple_type(args);
}

term_ref term_manager::get_tuple_type_element(term_ref tuple_type, size_t i) const {
  return d_tm->get_tuple_type_element(tuple_type, i);
}

term_ref term_manager::enum_type(const std::vector<std::string>& values) {
  return d_tm->enum_type(values);
}

size_t term_manager::get_enum_type_size(term_ref enum_type) const {
  const term& enum_type_term = d_tm->term_of(enum_type);
  assert(enum_type_term.op() == TYPE_ENUM);
  return enum_type_term.size();
}

term_ref term_manager::record_type(const id_to_term_map& fields) {
  return d_tm->record_type(fields);
}

term_ref term_manager::get_record_type_field_type(term_ref rec_type, std::string field) const {
  return d_tm->get_record_type_field_type(rec_type, field);
}

void term_manager::get_record_type_fields(term_ref rec_type, id_to_term_map& fields) const {
  return d_tm->get_record_type_fields(rec_type, fields);
}

term_ref term_manager::mk_struct_type(const std::vector<std::string>& names, const std::vector<term_ref>& types) {

  std::vector<term_ref> type_argumens;

  for (size_t i = 0; i < names.size(); ++ i) {
    type_argumens.push_back(mk_string_constant(names[i]));
    type_argumens.push_back(types[i]);
  }

  term_ref result = mk_term(TYPE_STRUCT, type_argumens);
  d_tm->typecheck(result);
  return result;
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

term_ref term_manager::mk_lambda(const std::vector<term_ref>& vars, term_ref body) {
  return d_tm->mk_abstraction(TERM_LAMBDA, vars, body);
}

term_ref term_manager::mk_exists(const std::vector<term_ref>& vars, term_ref body) {
  return d_tm->mk_abstraction(TERM_EXISTS, vars, body);
}

term_ref term_manager::mk_forall(const std::vector<term_ref>& vars, term_ref body) {
  return d_tm->mk_abstraction(TERM_FORALL, vars, body);
}

term_ref term_manager::mk_predicate_subtype(term_ref x, term_ref body) {
  std::vector<term_ref> vars;
  vars.push_back(x);
  return d_tm->mk_abstraction(TYPE_PREDICATE_SUBTYPE, vars, body);
}

term_ref term_manager::mk_array_lambda(term_ref i, term_ref body) {
  std::vector<term_ref> vars;
  vars.push_back(i);
  return d_tm->mk_abstraction(TERM_ARRAY_LAMBDA, vars, body);
}

size_t term_manager::get_lambda_arity(term_ref lambda) const {
  assert(term_of(lambda).op() == TERM_LAMBDA);
  return d_tm->get_abstraction_arity(lambda);
}

size_t term_manager::get_quantifier_arity(term_ref quantifier) const {
  assert(term_of(quantifier).op() == TERM_EXISTS || term_of(quantifier).op() == TERM_FORALL);
  return d_tm->get_abstraction_arity(quantifier);
}

term_ref term_manager::get_lambda_body(term_ref lambda) const {
  assert(term_of(lambda).op() == TERM_LAMBDA);
  return d_tm->get_abstraction_body(lambda);
}

term_ref term_manager::get_quantifier_body(term_ref quantifier) const {
  assert(term_of(quantifier).op() == TERM_EXISTS || term_of(quantifier).op() == TERM_FORALL);
  return d_tm->get_abstraction_body(quantifier);
}

term_ref term_manager::get_predicate_subtype_body(term_ref pred_type) const {
  assert(term_of(pred_type).op() == TYPE_PREDICATE_SUBTYPE);
  return d_tm->get_abstraction_body(pred_type);
}

term_ref term_manager::get_array_lambda_body(term_ref a_lambda) const {
  assert(term_of(a_lambda).op() == TERM_ARRAY_LAMBDA);
  return d_tm->get_abstraction_body(a_lambda);
}

term_ref term_manager::get_lambda_variable(term_ref lambda, size_t i) const {
  assert(term_of(lambda).op() == TERM_LAMBDA);
  return d_tm->get_abstraction_variable(lambda, i);
}

term_ref term_manager::get_quantifier_variable(term_ref quantifier, size_t i) const {
  assert(term_of(quantifier).op() == TERM_EXISTS || term_of(quantifier).op() == TERM_FORALL);
  return d_tm->get_abstraction_variable(quantifier, i);
}

term_ref term_manager::get_predicate_subtype_variable(term_ref subtype) const {
  assert(term_of(subtype).op() == TYPE_PREDICATE_SUBTYPE);
  return d_tm->get_abstraction_variable(subtype, 0);
}

term_ref term_manager::get_array_lambda_variable(term_ref a_lambda) const {
  assert(term_of(a_lambda).op() == TERM_ARRAY_LAMBDA);
  return d_tm->get_abstraction_variable(a_lambda, 0);
}

void term_manager::get_lambda_variables(term_ref lambda, std::vector<expr::term_ref>& vars_out) const {
  assert(term_of(lambda).op() == TERM_LAMBDA);
  d_tm->get_abstraction_variables(lambda, vars_out);
}

void term_manager::get_quantifier_variables(term_ref quantifer, std::vector<expr::term_ref>& vars_out) const {
  assert(term_of(quantifer).op() == TERM_EXISTS || term_of(quantifer).op() == TERM_FORALL);
  d_tm->get_abstraction_variables(quantifer, vars_out);
}

/** Get all fields of a struct variable */
void term_manager::get_struct_fields(const term& t, std::vector<term_ref>& out) const {
  for (size_t i = 0; i < get_struct_size(t); ++ i) {
    out.push_back(get_struct_field(t, i));
  }
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

term_ref term_manager::base_type_of(const term& t) const {
  return d_tm->base_type_of(t);
}

term_ref term_manager::tcc_of(const term& t) const {
  return d_tm->tcc_of(t);
}

size_t term_manager::id_of(term_ref ref) const {
  return d_tm->id_of(ref);
}

std::string term_manager::to_string(term_ref ref) const {
  std::stringstream ss;
  ss << set_tm(*const_cast<term_manager*>(this)) << ref;
  return ss.str();
}

void term_manager::use_namespace(std::string ns) {
  d_tm->use_namespace(ns);
}

void term_manager::pop_namespace() {
  d_tm->pop_namespace();
}

void term_manager::get_variables(term_ref ref, std::vector<term_ref>& out) const {
  d_tm->get_variables(ref, out);
}

void term_manager::get_variables(term_ref ref, std::set<term_ref>& out) const {
  d_tm->get_variables(ref, out);
}

size_t term_manager::get_variables_count(term_ref ref) const {
  std::vector<expr::term_ref> vars;
  get_variables(ref, vars);
  return vars.size();
}

struct all_matcher {
  bool operator() (const term_manager_internal::subterm_visitor_state& t) const {
    return true;
  }
  bool ignore(const term& t) const { return false; }
};

void term_manager::get_subterms(term_ref ref, std::vector<term_ref>& out) const {
  d_tm->get_subterms(ref, all_matcher(), out);
}

term_ref term_manager::substitute(term_ref t, const substitution_map& subst) {
  substitution_map subst_copy(subst);
  return d_tm->substitute(t, subst_copy);
}

term_ref term_manager::substitute_and_cache(term_ref t, substitution_map& subst) {
  return d_tm->substitute(t, subst);
}

term_ref term_manager::mk_not(term_ref f) {
  term_op op = d_tm->term_of(f).op();
  switch (op) {
  case TERM_NOT:
    return d_tm->term_of(f)[0];
  default:
    return mk_term(expr::TERM_NOT, f);
  }
}

void term_manager::get_conjuncts(term_ref f, std::set<term_ref>& out) {
  term_op op = d_tm->term_of(f).op();
  switch (op) {
  case TERM_AND: {
    size_t n = d_tm->term_of(f).size();
    for (size_t i = 0; i < n; ++ i) {
      get_conjuncts(d_tm->term_of(f)[i], out);
    }
    break;
  }
  case TERM_NOT: {
    std::set<term_ref> disjuncts;
    get_disjuncts(d_tm->term_of(f)[0], disjuncts);
    std::set<term_ref>::const_iterator it;
    for (it = disjuncts.begin(); it != disjuncts.end(); ++ it) {
      out.insert(mk_not(*it));
    }
    break;
  }
  default:
    out.insert(f);
  }
}

void term_manager::get_conjuncts(term_ref f, std::vector<term_ref>& out) {
  std::set<term_ref> conjuncts;
  get_conjuncts(f, conjuncts);
  std::copy(conjuncts.begin(), conjuncts.end(), std::back_inserter(out));
}


void term_manager::get_disjuncts(term_ref f, std::set<term_ref>& out) {
  term_op op = d_tm->term_of(f).op();
  switch (op) {
  case TERM_OR: {
    size_t n = d_tm->term_of(f).size();
    for (size_t i = 0; i < n; ++ i) {
      get_disjuncts(d_tm->term_of(f)[i], out);
    }
    break;
  }
  case TERM_NOT: {
    std::set<term_ref> conjuncts;
    get_conjuncts(d_tm->term_of(f)[0], conjuncts);
    std::set<term_ref>::const_iterator it;
    for (it = conjuncts.begin(); it != conjuncts.end(); ++ it) {
      out.insert(mk_not(*it));
    }
    break;
  }
  default:
    out.insert(f);
  }
}

term_ref term_manager::mk_and(const std::vector<term_ref>& conjuncts) {
  std::set<term_ref> lits;
  std::vector<term_ref>::const_iterator it;
  for (it = conjuncts.begin(); it != conjuncts.end(); ++ it) {
    get_conjuncts(*it, lits);
  }
  if (lits.size() == 0) {
    return mk_boolean_constant(true);
  }
  if (lits.size() == 1) {
    return *conjuncts.begin();
  }
  return d_tm->mk_term<TERM_AND>(lits.begin(), lits.end());
}

term_ref term_manager::mk_and(term_ref f1, term_ref f2) {
  std::vector<term_ref> conjuncts;
  conjuncts.push_back(f1);
  conjuncts.push_back(f2);
  return mk_and(conjuncts);
}

term_ref term_manager::mk_or(term_ref f1, term_ref f2) {
  std::vector<term_ref> disjuncts;
  disjuncts.push_back(f1);
  disjuncts.push_back(f2);
  return mk_or(disjuncts);
}

term_ref term_manager::mk_or(term_ref f) {
  std::vector<term_ref> disjuncts;
  disjuncts.push_back(f);
  return mk_or(disjuncts);
}

term_ref term_manager::mk_and(const std::set<term_ref>& conjuncts) {
  std::set<term_ref> lits;
  std::set<term_ref>::const_iterator it;
  for (it = conjuncts.begin(); it != conjuncts.end(); ++ it) {
    get_conjuncts(*it, lits);
  }
  if (lits.size() == 0) {
    return mk_boolean_constant(true);
  }
  if (lits.size() == 1) {
    return *lits.begin();
  }
  return d_tm->mk_term<TERM_AND>(lits.begin(), lits.end());
}

term_ref term_manager::mk_or(const std::vector<term_ref>& disjuncts) {
  std::set<term_ref> lits;
  std::vector<term_ref>::const_iterator it;
  for (it = disjuncts.begin(); it != disjuncts.end(); ++ it) {
    get_disjuncts(*it, lits);
  }
  if (lits.size() == 0) {
    return mk_boolean_constant(false);
  }
  if (lits.size() == 1) {
    return disjuncts[0];
  }
  return d_tm->mk_term<TERM_OR>(lits.begin(), lits.end());
}

bool term_manager::is_type(term_ref t) const {
  return d_tm->is_type(t);
}

bool term_manager::is_function_type(term_ref t) const {
  return d_tm->is_function_type(t);
}

bool term_manager::is_array_type(term_ref t) const {
  return d_tm->is_array_type(t);
}

bool term_manager::is_integer_type(term_ref t) const {
  return d_tm->is_integer_type(t);
}

bool term_manager::is_tuple_type(term_ref t) const {
  return d_tm->is_tuple_type(t);
}

bool term_manager::is_record_type(term_ref t) const {
  return d_tm->is_record_type(t);
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
  output::set_term_manager(out, &stm.d_tm);
  return out;
}

std::ostream& operator << (std::ostream& out, const set_output_language& stm) {
  output::set_output_language(out, stm.d_lang);
  return out;
}

void term_manager::gc() {
  TRACE("gc") << "term_manager::gc(): start" << std::endl;

  // Create the relocation map
  gc_relocator::relocation_map relocation_map;
  d_tm->gc(relocation_map);

  // Create the relocator to pass around
  gc_relocator gc_reloc(*this, relocation_map);

  // Collect with all participants
  std::set<gc_participant*>::iterator it = d_gc_participants.begin();
  for (; it != d_gc_participants.end(); ++ it) {
    (*it)->gc_collect(gc_reloc);
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

size_t term_manager::id() const {
  return d_id;
}

bool term_manager::compatible(term_ref t1, term_ref t2) {
  return d_tm->compatible(t1, t2);
}

}
}
