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
  d_stat_terms = new utils::stat_int("sally::expr::term_manager_internal::memory_size", 0);
  stats.add(d_stat_terms);

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

static
bool is_type(term_op op) {
  switch (op) {
  case TYPE_BOOL:
  case TYPE_INTEGER:
  case TYPE_REAL:
  case TYPE_STRUCT:
  case TYPE_BITVECTOR:
  case TYPE_STRING:
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

class type_computation_visitor {

  typedef boost::unordered_map<term_ref, term_ref, term_ref_hasher> term_to_term_map;

  /** The term manager */
  term_manager_internal& d_tm;

  /** Cache of the term manager */
  term_to_term_map& d_type_cache;

  /** Set to false whenever type computation fails */
  bool d_ok;

  /** Types of the children */
  std::vector<expr::term_ref> children_types;

  inline
  void error(expr::term_ref t_ref) const {
    std::stringstream ss;
    expr::term_manager* tm = output::get_term_manager(std::cerr);
    if (tm->get_internal() == &d_tm) {
      output::set_term_manager(ss, tm);
    }
    ss << "Can't typecheck " << t_ref << ".";
    throw exception(ss.str());
  }

  inline
  expr::term_ref type_of(expr::term_ref t_ref) const {
    term_to_term_map::const_iterator find = d_type_cache.find(t_ref);
    if (find == d_type_cache.end()) {
      error(t_ref);
    }
    return find->second;
  }

  inline
  const term& term_of(expr::term_ref t_ref) const {
    return d_tm.term_of(t_ref);
  }

public:

  type_computation_visitor(expr::term_manager_internal& tm, term_to_term_map& type_cache)
  : d_tm(tm)
  , d_type_cache(type_cache)
  , d_ok(true)
  {}

  /** Get the children of the term t that are relevant for the type computation */
  void get_children(expr::term_ref t, std::vector<expr::term_ref>& children) {
    const expr::term& t_term = d_tm.term_of(t);
    for (size_t i = 0; i < t_term.size(); ++ i) {
      children.push_back(t_term[i]);
    }
  }

  /** We visit only nodes that don't have types yet and are relevant for type computation */
  visitor_match_result match(term_ref t) {
    if (d_type_cache.find(t) == d_type_cache.end()) {
      // Visit the children if needed and then the node
      return VISIT_AND_CONTINUE;
    } else {
      // Don't visit children or this node or the node
      return DONT_VISIT_AND_BREAK;
    }
  }

  /** Visit the term, compute type (children already type-checked) */
  void visit(term_ref t_ref) {

    expr::term_ref t_type;

    TRACE("expr::types") << "compute_type::visit(" << t_ref << ")" << std::endl;

    // If typechecking failed, we just skip
    if (!d_ok) {
      return;
    }

    // The term we're typechecking (safe, since all subtypes already computed)
    const term& t = term_of(t_ref);
    term_op op = t.op();

    switch (op) {
    // Types -> TYPE_TYPE
    case TYPE_TYPE:
    case TYPE_BOOL:
    case TYPE_INTEGER:
    case TYPE_REAL:
    case TYPE_STRING:
      t_type = d_tm.type_type();
      break;
    case VARIABLE:
      // Type in payload
      t_type = t[0];
      break;
    case TYPE_BITVECTOR:
      d_ok = t.size() == 0 && d_tm.payload_of<size_t>(t) > 0;
      if (d_ok) t_type = d_tm.type_type();
      break;
    case TYPE_STRUCT: {
      if (t.size() % 2) {
        d_ok = false;
      } else {
        const term_ref* it = t.begin();
        for (bool even = true; d_ok && it != t.end(); even = !even, ++ it) {
          if (even) {
            d_ok = term_of(*it).op() == CONST_STRING;
          } else {
            d_ok = is_type(term_of(*it).op());
          }
        }
      }
      if (d_ok) t_type = d_tm.type_type();
      break;
    }
    // Equality
    case TERM_EQ: {
      if (t.size() != 2) {
        d_ok = false;
      } else {
        term_ref t0 = type_of(t[0]);
        term_ref t1 = type_of(t[1]);
        d_ok = d_tm.types_comparable(t0, t1);
      }
      if (d_ok) t_type = d_tm.boolean_type();
      break;
    }
    // ITE
    case TERM_ITE:
      if (t.size() != 3) {
        d_ok = false;
      } else {
        term_ref t0 = type_of(t[0]);
        term_ref t1 = type_of(t[1]);
        term_ref t2 = type_of(t[2]);
        d_ok = t0 == d_tm.boolean_type() && d_tm.types_comparable(t1, t2);
        if (d_ok) t_type = d_tm.supertype_of(t1, t2);
      }
      break;
    // Boolean terms
    case CONST_BOOL:
      t_type = d_tm.boolean_type();
      break;
    case TERM_AND:
    case TERM_OR:
    case TERM_XOR:
      if (t.size() < 2) {
        d_ok = false;
      } else {
        for (const term_ref* it = t.begin(); it != t.end(); ++ it) {
          if (type_of(*it) != d_tm.boolean_type()) {
            d_ok = false;
            break;
          }
        }
      }
      if (d_ok) t_type = d_tm.boolean_type();
      break;
    case TERM_NOT:
      if (t.size() != 1) {
        d_ok = false;
      } else {
        d_ok = type_of(t[0]) == d_tm.boolean_type();
      }
      if (d_ok) t_type = d_tm.boolean_type();
      break;
    case TERM_IMPLIES:
      if (t.size() != 2) {
        d_ok = false;
      } else {
        d_ok = type_of(t[0]) == d_tm.boolean_type() && type_of(t[1]) == d_tm.boolean_type();
      }
      if (d_ok) t_type = d_tm.boolean_type();
      break;
    // Arithmetic terms
    case CONST_RATIONAL:
      d_ok = true;
      t_type = d_tm.real_type();
      break;
    case TERM_ADD:
    case TERM_MUL:
      if (t.size() < 2) {
        d_ok = false;
      } else {
        term_ref max_type;
        for (const term_ref* it = t.begin(); it != t.end(); ++ it) {
          term_ref it_type = type_of(*it);
          if (!d_tm.is_subtype_of(it_type, d_tm.real_type())) {
            d_ok = false;
            break;
          } else {
            if (max_type.is_null()) {
              max_type = it_type;
            } else {
              max_type = d_tm.supertype_of(max_type, it_type);
            }
          }
        }
        if (d_ok) t_type = max_type;
      }
      break;
    case TERM_SUB:
      // 1 child is OK
      if (t.size() == 1) {
        term_ref t0 = type_of(t[0]);
        d_ok = d_tm.is_subtype_of(type_of(t[0]), d_tm.real_type());
        if (d_ok) t_type = t0;
      } else if (t.size() != 2) {
        d_ok = false;
      } else {
        term_ref t0 = type_of(t[0]);
        term_ref t1 = type_of(t[1]);
        d_ok = d_tm.is_subtype_of(t0, d_tm.real_type()) &&
               d_tm.is_subtype_of(t1, d_tm.real_type());
        if (d_ok) t_type = d_tm.supertype_of(t0, t1);
      }
      break;
    case TERM_LEQ:
    case TERM_LT:
    case TERM_GEQ:
    case TERM_GT:
      if (t.size() != 2) {
        d_ok = false;
      } else {
        term_ref t0 = type_of(t[0]);
        term_ref t1 = type_of(t[1]);
        d_ok = d_tm.is_subtype_of(t0, d_tm.real_type()) &&
               d_tm.is_subtype_of(t1, d_tm.real_type());
        if (d_ok) t_type = d_tm.boolean_type();
      }
      break;
    case TERM_DIV:
      if (t.size() != 2) {
        d_ok = false;
      } else {
        term_ref t0 = type_of(t[0]);
        term_ref t1 = type_of(t[1]);
        d_ok = d_tm.is_subtype_of(t0, d_tm.real_type()) &&
               d_tm.is_subtype_of(t1, d_tm.real_type());
        // TODO: make TCC
        if (d_ok) t_type = d_tm.supertype_of(t0, t1);
      }
      break;
    // Bitvector terms
    case CONST_BITVECTOR: {
      size_t size = d_tm.payload_of<bitvector>(t_ref).size();
      t_type = d_tm.bitvector_type(size);
      break;
    }
    case TERM_BV_NOT:
      if (t.size() != 1) {
        d_ok = false;
      } else {
        term_ref t0 = type_of(t[0]);
        d_ok = d_tm.is_bitvector_type(t0);
        if (d_ok) t_type = t0;
      }
      break;
    case TERM_BV_SUB:
      if (t.size() == 1) {
        term_ref t0 = type_of(t[0]);
        d_ok = d_tm.is_bitvector_type(t0);
        t_type = t0;
      } else if (t.size() == 2) {
        term_ref t0 = type_of(t[0]);
        term_ref t1 = type_of(t[1]);
        if (!d_tm.is_bitvector_type(t0)) {
          d_ok = false;
        } else {
          d_ok = t0 == t1;
        }
        if (d_ok) t_type = t0;
      } else {
        d_ok = false;
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
        d_ok = false;
      } else {
        const term_ref* it = t.begin();
        term_ref t0 = type_of(*it);
        if (!d_tm.is_bitvector_type(t0)) {
          d_ok = false;
        } else {
          d_ok = true;
          for (++ it; it != t.end(); ++ it) {
            if (type_of(*it) != t0) {
              d_ok = false;
              break;
            }
          }
        }
        if (d_ok) t_type = t0;
      }
      break;
    case TERM_BV_SHL:
    case TERM_BV_LSHR:
    case TERM_BV_ASHR:
    case TERM_BV_UDIV: // NOTE: Division x/0 = 11...11
    case TERM_BV_SDIV:
    case TERM_BV_UREM:
    case TERM_BV_SREM:
    case TERM_BV_SMOD:
      if (t.size() != 2) {
        d_ok = false;
      } else {
        term_ref t0 = type_of(t[0]);
        if (!d_tm.is_bitvector_type(t0)) {
          d_ok = false;
        } else {
          d_ok = t0 == type_of(t[1]);
        }
        if (d_ok) t_type = t0;
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
      if (t.size() != 2) {
        d_ok = false;
      } else {
        term_ref t0 = type_of(t[0]);
        if (!d_tm.is_bitvector_type(t0)) {
          d_ok = false;
        } else {
          d_ok = t0 == type_of(t[1]);
        }
        if (d_ok) t_type = d_tm.boolean_type();
      }
      break;
    case TERM_BV_CONCAT:
      if (t.size() < 2) {
        d_ok = false;
      } else {
        for (const term_ref* it = t.begin(); it != t.end(); ++ it) {
          if (!d_tm.is_bitvector_type(type_of(*it))) {
            d_ok = false;
          }
        }
        if (d_ok) {
          size_t size = 0;
          for (const term_ref* it = t.begin(); it != t.end(); ++ it) {
            term_ref it_type = type_of(*it);
            size += d_tm.bitvector_type_size(it_type);
          }
          t_type = d_tm.bitvector_type(size);
        }
      }
      break;
    case TERM_BV_EXTRACT:
      if (t.size() != 1) {
        d_ok = false;
      } else {
        term_ref t0 = type_of(t[0]);
        if (!d_tm.is_bitvector_type(t0)) {
          d_ok = false;
        } else {
          size_t child_size = d_tm.bitvector_type_size(t0);
          const bitvector_extract& extract = d_tm.payload_of<bitvector_extract>(t);
          if (extract.high < extract.low) {
            d_ok = false;
          } else {
            d_ok = extract.high < child_size;
            if (d_ok) {
              size_t size = extract.high - extract.low + 1;
              t_type = d_tm.bitvector_type(size);
            }
          }
        }
      }
      break;
    case CONST_STRING:
      d_ok = true;
      t_type = d_tm.string_type();
      break;
    default:
      assert(false);
    }

    TRACE("expr::types") << "compute_type::visit(" << t_ref << ") => " << t_type << std::endl;

    assert(!d_ok || !t_type.is_null());

    if (!d_ok) {
      error(t_ref);
    } else {
      assert(d_type_cache.find(t_ref) == d_type_cache.end());
      d_type_cache[t_ref] = t_type;
    }
  }
};

void term_manager_internal::compute_type(term_ref t) {
  if (d_type_cache.find(t) == d_type_cache.end()) {
    type_computation_visitor visitor(*this, d_type_cache);
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

