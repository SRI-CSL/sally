/*
 * term_manager_internal.cpp
 *
 *  Created on: Nov 17, 2014
 *      Author: dejan
 */

#include "expr/term_manager_internal.h"
#include "expr/term_manager.h"

#include "utils/exception.h"

#include <stack>
#include <sstream>

using namespace sal2;
using namespace expr;

term_manager_internal::term_manager_internal(bool typecheck)
: d_typecheck(typecheck)
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
    ok = (t.size() == 2 && type_of(t[0]) == type_of(t[1]));
    break;
  // ITE
  case TERM_ITE:
    ok = (t.size() == 3 && type_of(t[0]) == boolean_type() &&
        type_of(t[1]) == type_of(t[2]));
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
        if (type_of(*it) != real_type()) {
          ok = false;
          break;
        }
      }
    }
    break;
  case TERM_SUB:
    // 1 child is OK
    if (t.size() == 1) {
      ok = type_of(t[0]) == real_type();
    } else if (t.size() != 2) {
      ok = false;
    } else {
      ok = type_of(t[0]) == real_type() && type_of(t[1]) == real_type();
    }
    break;
  case TERM_LEQ:
  case TERM_LT:
  case TERM_GEQ:
  case TERM_GT:
    if (t.size() != 2) {
      ok = false;
    } else {
      ok = type_of(t[0]) == real_type() && type_of(t[1]) == real_type();
    }
    break;
  case TERM_DIV:
    if (t.size() != 2) {
      ok = false;
    } else {
      ok = type_of(t[0]) == real_type() && type_of(t[1]) == real_type();
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
  case TERM_BV_ADD:
  case TERM_BV_SUB:
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
    // TODO: fix this
    result = d_realType;
    break;
  case CONST_RATIONAL:
  case TERM_ADD:
  case TERM_MUL:
  case TERM_SUB:
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
std::string term_manager_internal::namespace_normalize(std::string id) const {
  for (size_t i = 0; i < d_namespaces.size(); ++ i) {
    std::string ns = d_namespaces[i];
    if (ns.size() < id.size() && id.substr(0, ns.size()) == ns) {
      id = id.substr(ns.size());
    }
  }
  return id;
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
