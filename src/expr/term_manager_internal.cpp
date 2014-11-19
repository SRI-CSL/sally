/*
 * term_manager_internal.cpp
 *
 *  Created on: Nov 17, 2014
 *      Author: dejan
 */

#include "expr/term_manager_internal.h"
#include "expr/term_manager.h"

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
  case CONST_STRING:
    ok = true;
    break;
  default:
    assert(false);
  }

  if (!ok) {
    std::cerr << "Can't typecheck: " << t_ref << std::endl;
  }
  assert(ok);

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
