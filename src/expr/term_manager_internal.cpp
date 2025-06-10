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

#include "expr/term_manager_internal.h"
#include "expr/term_manager.h"
#include "expr/term_visitor.h"
#include "expr/type_computation_visitor.h"

#include "utils/exception.h"
#include "utils/trace.h"

#include <stack>
#include <sstream>
#include <iostream>

using namespace sally;
using namespace expr;

term_manager_internal::term_manager_internal(utils::statistics& stats)
: d_name_transformer(0)
, d_stat_terms(0)
{
  // The null id
  new_term_id();

  // Initialize all payload memories to 0
  for (unsigned i = 0; i < OP_LAST; ++ i) {
    d_payload_memory[i] = 0;
  }

  // Statistic for size of term table
  d_stat_terms = static_cast<utils::stat_int*>(stats.register_stat("expr::term_manager_internal::memory_size"));
  d_stat_vars_bool = static_cast<utils::stat_int*>(stats.register_stat("expr::term_manager_internal::bool_vars"));
  d_stat_vars_real = static_cast<utils::stat_int*>(stats.register_stat("expr::term_manager_internal::real_vars"));
  d_stat_vars_int = static_cast<utils::stat_int*>(stats.register_stat("expr::term_manager_internal::int_vars"));

  // Create the types
  d_typeType = term_ref_strong(*this, mk_term<TYPE_TYPE>(alloc::empty_type()));
  d_booleanType = term_ref_strong(*this, mk_term<TYPE_BOOL>(alloc::empty_type()));
  d_integerType = term_ref_strong(*this, mk_term<TYPE_INTEGER>(alloc::empty_type()));
  d_realType = term_ref_strong(*this, mk_term<TYPE_REAL>(alloc::empty_type()));
  d_stringType = term_ref_strong(*this, mk_term<TYPE_STRING>(alloc::empty_type()));
}

term_manager_internal::~term_manager_internal() {
  for (unsigned i = 0; i < OP_LAST; ++ i) {
    delete d_payload_memory[i];
  }
}

term_ref term_manager_internal::tcc_of(const term& t) const {
  term_to_term_map::const_iterator find = d_tcc_map.find(ref_of(t));
  if (find == d_tcc_map.end()) {
    return term_ref();
  } else {
    return find->second;
  }
}

void term_manager_internal::compute_type(term_ref t) {
  if (d_type_cache.find(t) == d_type_cache.end()) {
    type_computation_visitor visitor(*this, d_type_cache, d_base_type_cache);
    term_visit_topological<type_computation_visitor, term_ref, term_ref_hasher> visit_topological(visitor);
    visit_topological.run(t);
  }
}

void term_manager_internal::typecheck(term_ref t_ref) {
  compute_type(t_ref);
}

void term_manager_internal::to_stream(std::ostream& out) const {
  out << "Term memory:" << std::endl;
  out << d_memory << std::endl;

  for (int op = 0; op < OP_LAST; ++ op) {
    out << "Payloads of :" << (term_op) op << std::endl;
    if (d_payload_memory[op]) {
      out << *d_payload_memory[op] << std::endl;
    } else {
      out << "null" << std::endl;
    }
  }

  out << "Terms:" << std::endl;
  for (term_ref_hash_set::const_iterator it = d_pool.begin(); it != d_pool.end(); ++ it) {
    out << "[id: " << it->id() << ", ref_count = " << d_term_refcount[it->id()] << "] : " << *it << std::endl;
  }
}

term_ref term_manager_internal::type_of(const term& t) {
  term_ref t_ref = ref_of(t);
  compute_type(t_ref);
  term_to_term_map::const_iterator find = d_type_cache.find(t_ref);
  assert (find != d_type_cache.end());
  return find->second;
}

term_ref term_manager_internal::type_of_if_exists(const term& t) const {
  term_ref t_ref = ref_of(t);
  term_to_term_map::const_iterator find = d_type_cache.find(t_ref);
  if (find == d_type_cache.end()) {
    return term_ref();
  } else {
    return find->second;
  }
}

term_ref term_manager_internal::base_type_of(const term& t) {
  // For types
  if (is_type(t)) {
    // For primitive types, we just get the type itself
    if (is_primitive_type(t)) {
      switch (t.op()) {
      case TYPE_INTEGER:
        // Base of integers is real
        return real_type();
      case TYPE_TYPE:
      case TYPE_BOOL:
      case TYPE_REAL:
      case TYPE_STRING:
      case TYPE_BITVECTOR:
      case TYPE_ENUM:
        return ref_of(t);
      default:
        assert(false);
        return ref_of(t);
      }
    }
    // Otherwise, compute the type, and get the base type
    term_ref t_ref = ref_of(t);
    compute_type(t_ref);
    term_to_term_map::const_iterator find = d_base_type_cache.find(t_ref);
    assert (find != d_base_type_cache.end());
    return find->second;
  } else {
    // For terms, just compute the type, and get the base type of the type
    term_ref t_ref = ref_of(t);
    compute_type(t_ref);
    return base_type_of(type_of(t));
  }
}

term_ref term_manager_internal::base_type_of_if_exists(const term& t) const {
  // For types
  if (is_type(t)) {
    // For primitive types, we just get the type itself
    if (is_primitive_type(t)) {
      switch (t.op()) {
      case TYPE_INTEGER:
        // Base of integers is real
        return real_type();
      case TYPE_TYPE:
      case TYPE_BOOL:
      case TYPE_REAL:
      case TYPE_STRING:
      case TYPE_BITVECTOR:
      case TYPE_ENUM:
        return ref_of(t);
      default:
        assert(false);
        return ref_of(t);
      }
    }
    // Otherwise, compute the type, and get the base type
    term_ref t_ref = ref_of(t);
    term_to_term_map::const_iterator find = d_base_type_cache.find(t_ref);
    if (find != d_base_type_cache.end()) {
      return find->second;
    } else {
      return term_ref();
    }
  } else {
    // For terms, just compute the type, and get the base type of the type
    return base_type_of_if_exists(type_of_if_exists(t));
  }
}


/** Add a namespace entry (will be removed from prefix when printing. */
void term_manager_internal::use_namespace(std::string ns) {
  d_namespaces.push_back(ns);
}

/** Pop the last added namespace */
void term_manager_internal::pop_namespace() {
  d_namespaces.pop_back();
}

/** Returns the id normalized with resepct to the current namespaces */
std::string term_manager_internal::name_normalize(std::string id) const {
  for (size_t i = 0; i < d_namespaces.size(); ++ i) {
    std::string ns = d_namespaces[i];
    if (ns.size() < id.size() && id.substr(0, ns.size()) == ns) {
      id = id.substr(ns.size());
    }
  }
  if (d_name_transformer) {
    return d_name_transformer->apply(id);
  } else {
    return id;
  }
}

// TODO: non-recursive
term_ref term_manager_internal::substitute(term_ref t, substitution_map& subst) {

  // Check if already there
  substitution_map::const_iterator it = subst.find(t);
  if (it != subst.end()) {
    return it->second;
  }

  bool child_changed = false;
  std::vector<term_ref> children;

  for (size_t i = 0; i < term_of(t).size(); ++ i) {
    // Substitute in the child
    term_ref child = term_of(t)[i];
    term_ref child_subst = substitute(child, subst);
    if (child_subst != child) {
      child_changed = true;
    }
    children.push_back(child_subst);
  }

  // Check if anything changed
  if (!child_changed) {
    subst[t] = t;
    return t;
  }

  // Something changed
  term_ref t_new;
  term_op op = term_of(t).op();
  // Need special cases for operators with payload
  switch (op) {
  case TERM_BV_EXTRACT: {
    // Make a copy, in case we resize on construction
    bitvector_extract extract = payload_of<bitvector_extract>(t);
    t_new = mk_term<TERM_BV_EXTRACT>(extract, children[0]);
    break;
  }
  case TERM_BV_SGN_EXTEND: {
    // Make a copy, in case we resize on construction
    bitvector_sgn_extend extend = payload_of<bitvector_sgn_extend>(t);
    t_new = mk_term<TERM_BV_SGN_EXTEND>(extend, children[0]);
    break;
  }
  default:
    t_new = mk_term(op, children.begin(), children.end());
  }
  subst[t] = t_new;

  // Return the result
  return t_new;
}

term_ref term_manager_internal::bitvector_type(size_t size) {
   bitvector_type_map::const_iterator find = d_bitvectorType.find(size);
   if (find!= d_bitvectorType.end()) return find->second;
   term_ref new_type = mk_term<TYPE_BITVECTOR>(size);
   d_bitvectorType[size] = term_ref_strong(*this, new_type);
   return new_type;
}

bool term_manager_internal::is_integer_type(term_ref t) const {
  const term& t_term = term_of(t);
  if (t_term.d_op == TYPE_INTEGER) return true;
  if (t_term.d_op == TYPE_PREDICATE_SUBTYPE) {
    term_ref var = t_term[0];
    term_ref var_type = type_of_if_exists(var);
    assert(!var_type.is_null());
    return  is_integer_type(var_type);
  }
  return false;
}

bool term_manager_internal::is_real_type(term_ref t) const {
  return term_of(t).d_op == TYPE_REAL;
}

bool term_manager_internal::is_boolean_type(term_ref t) const {
  return term_of(t).d_op == TYPE_BOOL;
}

bool term_manager_internal::is_bitvector_type(term_ref t) const {
  return term_of(t).d_op == TYPE_BITVECTOR;
}

bool term_manager_internal::is_array_type(term_ref t) const {
  return term_of(t).d_op == TYPE_ARRAY;
}

bool term_manager_internal::is_function_type(term_ref t) const {
  return term_of(t).d_op == TYPE_FUNCTION;
}

bool term_manager_internal::is_tuple_type(term_ref t) const {
  return term_of(t).d_op == TYPE_TUPLE;
}

bool term_manager_internal::is_record_type(term_ref t) const {
  return term_of(t).d_op == TYPE_RECORD;
}

bool term_manager_internal::is_enum_type(term_ref t) const {
  return  term_of(t).d_op == TYPE_ENUM;
}

bool term_manager_internal::is_type(const term& t) {
  switch (t.op()) {
  case TYPE_TYPE:
  case TYPE_BOOL:
  case TYPE_INTEGER:
  case TYPE_REAL:
  case TYPE_STRING:
  case TYPE_BITVECTOR:
  case TYPE_STRUCT:
  case TYPE_TUPLE:
  case TYPE_RECORD:
  case TYPE_ENUM:
  case TYPE_FUNCTION:
  case TYPE_ARRAY:
  case TYPE_PREDICATE_SUBTYPE:
    return true;
  default:
    return false;
  }
}

bool term_manager_internal::is_primitive_type(const term& t) {
  switch (t.op()) {
  case TYPE_TYPE:
  case TYPE_BOOL:
  case TYPE_INTEGER:
  case TYPE_REAL:
  case TYPE_STRING:
  case TYPE_BITVECTOR:
  case TYPE_ENUM:
    return true;
  default:
    return false;
  }
}

size_t term_manager_internal::bitvector_type_size(term_ref t_ref) const {
  const term& t = term_of(t_ref);
  assert(t.op() == TYPE_BITVECTOR);
  return payload_of<size_t>(t);
}

term_ref term_manager_internal::function_type(const std::vector<term_ref>& args) {
  term_ref result = mk_term<TYPE_FUNCTION>(args.begin(), args.end());
  typecheck(result);
  return result;
}

term_ref term_manager_internal::get_function_type_domain(term_ref fun_type, size_t i) const {
  const term& t = term_of(fun_type);
  assert(t.op() == TYPE_FUNCTION);
  assert(i + 1 < t.size());
  return t[i];
}

term_ref term_manager_internal::get_function_type_codomain(term_ref fun_type) const {
  const term& t = term_of(fun_type);
  assert(t.op() == TYPE_FUNCTION);
  return t[t.size() - 1];
}

term_ref term_manager_internal::array_type(term_ref index_type, term_ref element_type) {
  term_ref result = mk_term<TYPE_ARRAY>(index_type, element_type);
  typecheck(result);
  return result;
}

term_ref term_manager_internal::get_array_type_index(term_ref arr_type) const {
  const term& t = term_of(arr_type);
  assert(t.op() == TYPE_ARRAY);
  return t[0];
}

term_ref term_manager_internal::get_array_type_element(term_ref arr_type) const {
  const term& t = term_of(arr_type);
  assert(t.op() == TYPE_ARRAY);
  return t[1];
}

term_ref term_manager_internal::tuple_type(const std::vector<term_ref>& args) {
  term_ref result = mk_term<TYPE_TUPLE>(args.begin(), args.end());
  typecheck(result);
  return result;
}

term_ref term_manager_internal::get_tuple_type_element(term_ref tuple_type, size_t i) const {
  const term& t = term_of(tuple_type);
  assert(t.op() == TYPE_TUPLE);
  assert(i < t.size());
  return t[i];
}

term_ref term_manager_internal::enum_type(const std::vector<std::string>& values) {
  std::vector<term_ref> string_values;
  for (size_t i = 0; i < values.size(); ++ i) {
    string_values.push_back(mk_term<CONST_STRING>(values[i]));
  }
  term_ref result = mk_term<TYPE_ENUM>(string_values.begin(), string_values.end());
  typecheck(result);
  return result;
}

term_ref term_manager_internal::record_type(const id_to_term_map& fields) {
  std::vector<term_ref> elements;
  id_to_term_map::const_iterator it = fields.begin(), end = fields.end();
  for (; it != end; ++ it) {
    term_ref id = mk_term<CONST_STRING>(it->first);
    term_ref type = it->second;
    elements.push_back(id);
    elements.push_back(type);
  }
  term_ref result = mk_term<TYPE_RECORD>(elements.begin(), elements.end());
  typecheck(result);
  return result;
}

term_ref term_manager_internal::get_record_type_field_type(term_ref rec_type, std::string field) const {
  const term& rec_type_term = term_of(rec_type);
  assert(rec_type_term.op() == TYPE_RECORD);
  for (size_t i = 0; i < rec_type_term.size(); i += 2) {
    std::string id = payload_of<utils::string>(rec_type_term[i]);
    if (id == field) {
      return rec_type_term[i+1];
    }
  }
  return term_ref();
}

void term_manager_internal::get_record_type_fields(term_ref rec_type, id_to_term_map& fields) const {
  const term& rec_type_term = term_of(rec_type);
  assert(rec_type_term.op() == TYPE_RECORD);
  for (size_t i = 0; i < rec_type_term.size(); i += 2) {
    std::string id = payload_of<utils::string>(rec_type_term[i]);
    term_ref type = rec_type_term[i+1];
    fields[id] = type;
  }
}


term_ref term_manager_internal::get_default_value(term_ref type_ref) {
  const term& type = term_of(type_ref);
  term_op op = type.op();
  switch (op) {
  case TYPE_BOOL:
    return mk_term<CONST_BOOL>(false);
  case TYPE_INTEGER:
  case TYPE_REAL:
    return mk_term<CONST_RATIONAL>(rational());
  case TYPE_BITVECTOR: {
    size_t size = payload_of<size_t>(type);
    return mk_term<CONST_BITVECTOR>(bitvector(size));
  }
  default:
    assert(false);
  }
  return term_ref();
}

void term_manager_internal::set_name_transformer(const utils::name_transformer* transformer) {
  d_name_transformer = transformer;
}

const utils::name_transformer* term_manager_internal::get_name_transformer() const {
  return d_name_transformer;
}

void term_manager_internal::gc(std::map<expr::term_ref, expr::term_ref>& reloc_map) {
  assert(reloc_map.empty());

  TRACE("gc") << "term_manager_internal::gc(): begin" << std::endl;

  typedef boost::unordered_set<term_ref, term_ref_hasher> visited_set;

  // Queue of terms to visit
  std::queue<term_ref> queue;

  // Terms we've visited already
  visited_set visited_terms;

  // Payloads that we've visited one set per term_op
  visited_set visited_payloads[OP_LAST];

  // Go though all ids and get the terms with refcount > 0
  tref_id_map::const_iterator terms_it = d_term_ids.begin(), terms_it_end = d_term_ids.end();
  for (; terms_it != terms_it_end; ++ terms_it) {
    assert(terms_it->second < d_term_refcount.size());
    if (d_term_refcount[terms_it->second] > 0) {
      term_ref t = terms_it->first;
      queue.push(t);
      visited_terms.insert(t);
    }
  }

  // Traverse the terms and collect all subterms and payloads
  while (!queue.empty()) {

    // Process current
    term_ref current = queue.front();
    queue.pop();

    // Add any unvisited children
    const term& current_term = term_of(current);
    for (size_t i = 0; i < current_term.size(); ++ i) {
      if (visited_terms.find(current_term[i]) == visited_terms.end()) {
        queue.push(current_term[i]);
        visited_terms.insert(current_term[i]);
      }
    }

    // Add payload if any
    term_op op = current_term.op();
    if (d_payload_memory[op]) {
      visited_payloads[op].insert(*current_term.end());
    }
  }

  TRACE("gc") << "term_manager_internal::gc(): end" << std::endl;
}

term_ref term_manager_internal::mk_abstraction(term_op op, const std::vector<term_ref>& vars, term_ref body) {

  std::vector<term_ref> children(vars.begin(), vars.end());
  children.push_back(body);

  // Make the term
  term_ref result;
  const std::vector<term_ref>::const_iterator begin = children.begin(), end = children.end();
  switch (op) {
  case TERM_LAMBDA:
    result = mk_term<TERM_LAMBDA>(begin, end);
    break;
  case TERM_EXISTS:
    result = mk_term<TERM_EXISTS>(begin, end);
    break;
  case TERM_FORALL:
    result = mk_term<TERM_FORALL>(begin, end);
    break;
  case TYPE_PREDICATE_SUBTYPE:
    result = mk_term<TYPE_PREDICATE_SUBTYPE>(begin, end);
    break;
  case TERM_ARRAY_LAMBDA:
    result = mk_term<TERM_ARRAY_LAMBDA>(begin, end);
    break;
  default:
    assert(false);
  }

  // Typecheck
  typecheck(result);

  // Done
  return result;
}

bool term_manager_internal::is_abstraction(const term& t) const {
  switch (t.op()) {
  case TERM_LAMBDA:
  case TERM_EXISTS:
  case TERM_FORALL:
  case TYPE_PREDICATE_SUBTYPE:
  case TERM_ARRAY_LAMBDA:
    return true;
  default:
    return false;
  }
}

term_ref term_manager_internal::get_abstraction_body(term_ref abstraction) const {
  const term& t = term_of(abstraction);
  assert(is_abstraction(t));
  assert(t.size() > 2);
  return t[t.size() - 1];
}

size_t term_manager_internal::get_abstraction_arity(term_ref abstraction) const {
  const term& t = term_of(abstraction);
  assert(is_abstraction(t));
  assert(t.size() >= 2); // At least term and one argument
  return t.size() - 1;
}

term_ref term_manager_internal::get_abstraction_variable(term_ref abstraction, size_t i) const {
  const term& t = term_of(abstraction);
  assert(is_abstraction(t));
  return t[i];
}

bool term_manager_internal::compatible(term_ref t1, term_ref t2) {
  if (t1 == t2) return true;
  return base_type_of(t1) == base_type_of(t2);
}
