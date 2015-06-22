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

#include "utils/exception.h"
#include "utils/trace.h"

#include <stack>
#include <sstream>
#include <iostream>

using namespace sally;
using namespace expr;

term_manager_internal::term_manager_internal()
: d_name_transformer(0)
{
  // The null id
  new_term_id();

  // Initialize all payload memories to 0
  for (unsigned i = 0; i < OP_LAST; ++ i) {
    d_payload_memory[i] = 0;
  }

  // Create the types
  d_booleanType = term_ref_strong(*this, mk_term<TYPE_BOOL>(alloc::empty_type()));
  d_integerType = term_ref_strong(*this, mk_term<TYPE_INTEGER>(alloc::empty_type()));
  d_realType = term_ref_strong(*this, mk_term<TYPE_REAL>(alloc::empty_type()));
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

static
bool is_type(term_op op) {
  switch (op) {
  case TYPE_BOOL:
  case TYPE_INTEGER:
  case TYPE_REAL:
  case TYPE_STRUCT:
  case TYPE_BITVECTOR:
    return true;
  default:
    return false;
  }
}

bool term_manager_internal::is_subtype_of(term_ref t1, term_ref t2) const {
  if (t1 == t2) {
    return true;
  }
  if (t1 == integer_type() && t2 == real_type()) {
    return true;
  }
  return false;
}

term_ref term_manager_internal::supertype_of(term_ref t1, term_ref t2) const {
  assert(types_comparable(t1, t2));

  if (t1 == t2) {
    return t1;
  }
  if (t1 == integer_type() && t2 == real_type()) {
    return t2;
  }
  if (t2 == integer_type() && t1 == real_type()) {
    return t1;
  }

  assert(false);
  return t1;
}

bool term_manager_internal::types_comparable(term_ref t1, term_ref t2) const {
  return (is_subtype_of(t1, t2) || is_subtype_of(t2, t1));
}

bool term_manager_internal::typecheck(term_ref t_ref) {
  const term& t = term_of(t_ref);
  term_op op = t.op();

  bool ok = true;

  switch (op) {
  case TYPE_BOOL:
  case TYPE_INTEGER:
  case TYPE_REAL:
  case VARIABLE:
    break;
  case TYPE_BITVECTOR:
    ok = t.size() == 0 && payload_of<size_t>(t) > 0;
    break;
  case TYPE_STRUCT: {
    if (t.size() % 2) {
      ok = false;
    } else {
      for (size_t i = 0; ok && i < t.size(); ++ i) {
        if (i % 2 == 0) {
          ok = term_of(t[i]).op() == CONST_STRING;
        } else {
          ok = is_type(term_of(t[i]).op());
        }
      }
    }
    break;
  }
  // Equality
  case TERM_EQ:
    ok = (t.size() == 2 && types_comparable(type_of(t[0]), type_of(t[1])));
    break;
  // ITE
  case TERM_ITE:
    ok = (t.size() == 3 &&
        type_of(t[0]) == boolean_type() &&
        types_comparable(type_of(t[1]), type_of(t[2])));
    break;
  // Boolean terms
  case CONST_BOOL:
    break;
  case TERM_AND:
  case TERM_OR:
  case TERM_XOR:
    if (t.size() < 2) {
      ok = false;
    } else {
      for (const term_ref* it = t.begin(); it != t.end(); ++ it) {
        if (type_of(*it) != boolean_type()) {
          ok = false;
          break;
        }
      }
    }
    break;
  case TERM_NOT:
    if (t.size() != 1) {
      ok = false;
    } else {
      ok = type_of(t[0]) == boolean_type();
    }
    break;
  case TERM_IMPLIES:
    if (t.size() != 2) {
      ok = false;
    } else {
      ok = type_of(t[0]) == boolean_type() && type_of(t[1]) == boolean_type();
    }
    break;
  // Arithmetic terms
  case CONST_INTEGER:
  case CONST_RATIONAL:
    break;
  case TERM_ADD:
  case TERM_MUL:
    if (t.size() < 2) {
      ok = false;
    } else {
      for (const term_ref* it = t.begin(); it != t.end(); ++ it) {
        term_ref it_type = type_of(*it);
        if (!is_subtype_of(it_type, real_type())) {
          ok = false;
          break;
        }
      }
    }
    break;
  case TERM_SUB:
    // 1 child is OK
    if (t.size() == 1) {
      ok = is_subtype_of(type_of(t[0]), real_type());
    } else if (t.size() != 2) {
      ok = false;
    } else {
      ok = is_subtype_of(type_of(t[0]), real_type()) &&
           is_subtype_of(type_of(t[1]), real_type());
    }
    break;
  case TERM_LEQ:
  case TERM_LT:
  case TERM_GEQ:
  case TERM_GT:
    if (t.size() != 2) {
      ok = false;
    } else {
      ok = is_subtype_of(type_of(t[0]), real_type()) &&
           is_subtype_of(type_of(t[1]), real_type());
    }
    break;
  case TERM_DIV:
    if (t.size() != 2) {
      ok = false;
    } else {
      ok = is_subtype_of(type_of(t[0]), real_type()) &&
           is_subtype_of(type_of(t[1]), real_type());
      // TODO: make TCC
    }
    break;
  // Bitvector terms
  case CONST_BITVECTOR:
    ok = true;
    break;
  case TERM_BV_NOT:
    ok = t.size() == 1 && is_bitvector_type(type_of(t[0]));
    break;
  case TERM_BV_SUB:
    if (t.size() == 1) {
      ok = is_bitvector_type(type_of(t[0]));
    } else if (t.size() == 2) {
      term_ref type_ref = type_of(t[0]);
      if (!is_bitvector_type(type_ref)) {
        ok = false;
      } else {
        ok = type_ref == type_of(t[1]);
      }
    } else {
      ok = false;
    }
    break;
  case TERM_BV_ADD:
  case TERM_BV_MUL:
  case TERM_BV_XOR:
  case TERM_BV_AND:
  case TERM_BV_OR:
  case TERM_BV_NAND:
  case TERM_BV_NOR:
  case TERM_BV_XNOR:
    if (t.size() < 2) {
      ok = false;
    } else {
      const term_ref* it = t.begin();
      term_ref type_ref = type_of(*it);
      if (!is_bitvector_type(type_ref)) {
        ok = false;
      } else {
        ok = true;
        for (++ it; it != t.end(); ++ it) {
          if (type_of(*it) != type_ref) {
            ok = false;
            break;
          }
        }
      }
    }
    break;
  case TERM_BV_SHL:
  case TERM_BV_LSHR:
  case TERM_BV_ASHR:
    if (t.size() != 2) {
      ok = false;
    } else {
      term_ref type_ref = type_of(t[0]);
      if (!is_bitvector_type(type_ref)) {
        ok = false;
      } else {
        ok = type_ref == type_of(t[1]);
      }
    }
    break;
  case TERM_BV_ULEQ:
  case TERM_BV_SLEQ:
  case TERM_BV_ULT:
  case TERM_BV_SLT:
  case TERM_BV_UGEQ:
  case TERM_BV_SGEQ:
  case TERM_BV_UGT:
  case TERM_BV_SGT:
  case TERM_BV_UDIV: // NOTE: Division x/0 = 11...11
  case TERM_BV_SDIV:
  case TERM_BV_UREM:
  case TERM_BV_SREM:
  case TERM_BV_SMOD:
    if (t.size() != 2) {
      ok = false;
    } else {
      term_ref type_ref = type_of(t[0]);
      if (!is_bitvector_type(type_ref)) {
        ok = false;
      } else {
        ok = type_ref == type_of(t[1]);
      }
    }
    break;
  case TERM_BV_CONCAT:
    if (t.size() < 2) {
      ok = false;
    } else {
      ok = true;
      for (const term_ref* it = t.begin(); it != t.end(); ++ it) {
        if (!is_bitvector_type(type_of(*it))) {
          ok = false;
        }
      }
    }
    break;
  case TERM_BV_EXTRACT:
    if (t.size() != 1) {
      ok = false;
    } else {
      term_ref child_type = type_of(t[0]);
      if (!is_bitvector_type(child_type)) {
        ok = false;
      } else {
        size_t child_size = bitvector_type_size(child_type);
        const bitvector_extract& extract = payload_of<bitvector_extract>(t);
        if (extract.high < extract.low) {
          ok = false;
        } else {
          ok = extract.high < child_size;
        }
      }
    }
    break;
  case CONST_STRING:
    ok = true;
    break;
  default:
    assert(false);
  }

  if (!ok) {
    std::stringstream ss;
    output::set_term_manager(ss, this);
    ss << "Can't typecheck " << t_ref << ".";
    throw exception(ss.str());
  }

  return ok;
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

std::string term_manager_internal::to_string(term_ref ref) const {
  std::stringstream ss;
  ss << set_tm(*this) << ref;
  return ss.str();
}

term_ref term_manager_internal::type_of(const term& t) const {

  // Reference of t
  term_ref t_ref = ref_of(t);

  // Check if computed already
  term_to_term_map::const_iterator find = d_type_cache.find(t_ref);
  if (find != d_type_cache.end()) {
    return find->second;
  }

  // The result
  term_ref result = term_ref();

  // Compute the type
  switch (t.op()) {
  case TYPE_BOOL:
  case TYPE_INTEGER:
  case TYPE_REAL:
  case TYPE_STRUCT:
    result = term_ref();
    break;
  case VARIABLE:
    result = t[0];
    break;
  // Equality
  case TERM_EQ:
    result = boolean_type();
    break;
  // ITE
  case TERM_ITE:
    result = type_of(t[1]);
    break;
  // Boolean terms
  case CONST_BOOL:
  case TERM_AND:
  case TERM_OR:
  case TERM_XOR:
  case TERM_NOT:
  case TERM_IMPLIES:
    result = boolean_type();
    break;
  // Arithmetic terms
  case CONST_INTEGER:
    result = d_integerType;
    break;
  case CONST_RATIONAL:
    result = d_realType;
    break;
  case TERM_ADD:
  case TERM_MUL:
  case TERM_SUB: {
    // If all children are integer, it's integer
    result = integer_type();
    for (const term_ref* it = t.begin(); it != t.end(); ++ it) {
      if (type_of(*it) != integer_type()) {
        result = real_type();
        break;
      }
    }
    break;
  }
  case TERM_DIV:
    result = d_realType;
    break;
  case TERM_LEQ:
  case TERM_LT:
  case TERM_GEQ:
  case TERM_GT:
    result = d_booleanType;
    break;
  case CONST_BITVECTOR:
    result = const_cast<term_manager_internal*>(this)->bitvector_type(payload_of<bitvector>(t).size());
    break;

  case TERM_BV_ADD:
  case TERM_BV_SUB:
  case TERM_BV_MUL:
  case TERM_BV_XOR:
  case TERM_BV_NOT:
  case TERM_BV_AND:
  case TERM_BV_OR:
  case TERM_BV_NAND:
  case TERM_BV_NOR:
  case TERM_BV_XNOR:
  case TERM_BV_UDIV:
  case TERM_BV_SDIV:
  case TERM_BV_UREM:
  case TERM_BV_SREM:
  case TERM_BV_SMOD:
    result = type_of(t[0]);
    break;
  case TERM_BV_ULEQ:
  case TERM_BV_SLEQ:
  case TERM_BV_ULT:
  case TERM_BV_SLT:
  case TERM_BV_UGEQ:
  case TERM_BV_SGEQ:
  case TERM_BV_UGT:
  case TERM_BV_SGT:
    result = boolean_type();
    break;
  case TERM_BV_SHL:
  case TERM_BV_LSHR:
  case TERM_BV_ASHR:
    result = type_of(t[0]);
    break;
  case TERM_BV_CONCAT: {
    size_t size = 0;
    for (const term_ref* it = t.begin(); it != t.end(); ++ it) {
      term_ref type_ref = type_of(*it);
      size += bitvector_type_size(type_ref);
    }
    result = const_cast<term_manager_internal*>(this)->bitvector_type(size);
    break;
  }
  case TERM_BV_EXTRACT: {
    const bitvector_extract& extract = payload_of<bitvector_extract>(t);
    size_t size = extract.high - extract.low + 1;
    result = const_cast<term_manager_internal*>(this)->bitvector_type(size);
    break;
  }
  case CONST_STRING:
    break;
  default:
    assert(false);
  }

  // Cache
  const_cast<term_manager_internal*>(this)->d_type_cache[t_ref] = result;

  return result;
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
  case TERM_BV_EXTRACT:
    t_new = mk_term<TERM_BV_EXTRACT>(payload_of<bitvector_extract>(t), children.begin(), children.end());
    break;
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

bool term_manager_internal::is_bitvector_type(term_ref t) const {
  return term_of(t).d_op == TYPE_BITVECTOR;
}

size_t term_manager_internal::bitvector_type_size(term_ref t_ref) const {
  const term& t = term_of(t_ref);
  assert(t.op() == TYPE_BITVECTOR);
  return payload_of<size_t>(t);
}

term_ref term_manager_internal::get_default_value(term_ref type_ref) {
  const term& type = term_of(type_ref);
  term_op op = type.op();
  switch (op) {
  case TYPE_BOOL:
    return mk_term<CONST_BOOL>(false);
  case TYPE_INTEGER:
    return mk_term<CONST_INTEGER>(integer());
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

