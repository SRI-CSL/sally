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
  tcc_map::const_iterator find = d_tcc_map.find(ref_of(t));
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
    ok = (t.size() == 3 && type_of(t[0]) == booleanType() &&
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
        if (type_of(*it) != booleanType()) {
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
      ok = type_of(t[0]) == booleanType();
    }
    break;
  case TERM_IMPLIES:
    if (t.size() != 2) {
      ok = false;
    } else {
      ok = type_of(t[0]) == booleanType() && type_of(t[1]) == booleanType();
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
        if (type_of(*it) != realType()) {
          ok = false;
          break;
        }
      }
    }
    break;
  case TERM_SUB:
    // 1 child is OK
    if (t.size() == 1) {
      ok = type_of(t[0]) == realType();
    } else if (t.size() != 2) {
      ok = false;
    } else {
      ok = type_of(t[0]) == realType() && type_of(t[1]) == realType();
    }
    break;
  case TERM_LEQ:
  case TERM_LT:
  case TERM_GEQ:
  case TERM_GT:
    if (t.size() != 2) {
      ok = false;
    } else {
      ok = type_of(t[0]) == realType() && type_of(t[1]) == realType();
    }
    break;
  case TERM_DIV:
    if (t.size() != 2) {
      ok = false;
    } else {
      ok = type_of(t[0]) == realType() && type_of(t[1]) == realType();
      // TODO: make TCC
    }
    break;
  // Bitvector terms
  case CONST_BITVECTOR:
    ok = true;
    break;
  case TERM_BV_NOT:
    ok = false;
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
    ok = false;
    break;
  case TERM_BV_SHL:
  case TERM_BV_LSHR:
  case TERM_BV_ASHR:
    ok = false;
    break;
  case TERM_BV_U_LEQ:
  case TERM_BV_S_LEQ:
  case TERM_BV_U_LT:
  case TERM_BV_S_LT:
  case TERM_BV_U_GEQ:
  case TERM_BV_S_GEQ:
  case TERM_BV_U_GT:
  case TERM_BV_S_GT:
      ok = false;
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
  switch (t.op()) {
  case TYPE_BOOL:
  case TYPE_INTEGER:
  case TYPE_REAL:
  case TYPE_STRUCT:
    return term_ref();
  case VARIABLE:
    return t[0];
  // Equality
  case TERM_EQ:
    return booleanType();
    break;
  // ITE
  case TERM_ITE:
    return type_of(t[1]);
  // Boolean terms
  case CONST_BOOL:
  case TERM_AND:
  case TERM_OR:
  case TERM_XOR:
  case TERM_NOT:
  case TERM_IMPLIES:
    return booleanType();
  // Arithmetic terms
  case CONST_INTEGER:
    // TODO: fix this
    return d_realType;
  case CONST_RATIONAL:
  case TERM_ADD:
  case TERM_MUL:
  case TERM_SUB:
  case TERM_DIV:
    return d_realType;
  case TERM_LEQ:
  case TERM_LT:
  case TERM_GEQ:
  case TERM_GT:
    return d_booleanType;
  case CONST_STRING:
    return term_ref();
  default:
    assert(false);
  }
  return term_ref();
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
  term_ref t_new = mk_term(term_of(t).op(), children.begin(), children.end());
  subst[t] = t_new;

  // Return the result
  return t_new;
}

term_ref term_manager_internal::bitvectorType(size_t size) {
   bitvector_type_map::const_iterator find = d_bitvectorType.find(size);
   if (find!= d_bitvectorType.end()) return find->second;
   term_ref new_type = mk_term<TYPE_BITVECTOR>(size);
   d_bitvectorType[size] = term_ref_strong(*this, new_type);
   return new_type;
}
