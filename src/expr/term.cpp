/*
 * term.cpp
 *
 *  Created on: Oct 2, 2014
 *      Author: dejan
 */

#include "expr/term.h"
#include "utils/output.h"

#include <iomanip>
#include <cassert>

namespace sal2 {
namespace expr {

term_manager::term_manager(bool typecheck)
: d_typecheck(typecheck)
{
  // Initalize all payload memory to 0
  for (unsigned i = 0; i < OP_LAST; ++ i) {
    d_payload_memory[i] = 0;
  }

  // Create the types
  d_booleanType = mk_term<OP_TYPE_BOOL>(alloc::empty);
  d_integerType = mk_term<OP_TYPE_INTEGER>(alloc::empty);
  d_realType = mk_term<OP_TYPE_REAL>(alloc::empty);
}

void term_ref::to_stream(std::ostream& out) const {
  if (is_null()) {
    out << "null";
  } else {
    const term_manager* tm = output::get_term_manager(out);
    if (tm == 0) {
      out << d_ref;
    } else {
      tm->term_of(*this).to_stream(out);
    }
  }
}

void term::to_stream(std::ostream& out) const {
  output::language lang = output::get_output_language(out);
  const term_manager* tm = output::get_term_manager(out);
  switch (lang) {
  case output::SMTLIB:
    to_stream_smt(out, *tm);
    break;
  default:
    assert(false);
  }
}

static inline
std::string get_smt_keyword(term_op op) {
  switch (op) {
  case OP_AND:
    return "and";
  case OP_OR:
    return "or";
  case OP_NOT:
    return "not";
  case OP_IMPLIES:
    return "implies";
  case OP_XOR:
    return "xor";
  case OP_ADD:
    return "+";
  case OP_SUB:
    return "-";
  case OP_MUL:
    return "*";
  case OP_DIV:
    return "/";
  case OP_TYPE_BOOL:
    return "Bool";
  case OP_TYPE_INTEGER:
    return "Integer";
  case OP_TYPE_REAL:
    return "Real";
  default:
    assert(false);
    return "unknown";
  }
}

void term::to_stream_smt(std::ostream& out, const term_manager& tm) const {
  switch (d_op) {
  case OP_VARIABLE:
    out << tm.payload_of<std::string>(*this);
    break;
  case OP_BOOL_CONSTANT:
    out << (tm.payload_of<bool>(*this) ? "true" : "false");
    break;
  case OP_AND:
  case OP_OR:
  case OP_NOT:
  case OP_IMPLIES:
  case OP_XOR:
  case OP_ADD:
  case OP_SUB:
  case OP_MUL:
  case OP_DIV: {
    if (size() > 0) {
      out << "(";
    }
    out << get_smt_keyword(d_op);
    for (const term_ref* it = begin(); it != end(); ++ it) {
      out << " " << *it;
    }
    if (size() > 0) {
      out << ")";
    }
    break;
  }
  case OP_REAL_CONSTANT:
    // Stream is already in SMT mode
    out << tm.payload_of<rational>(*this);
    break;
  default:
    assert(false);
  }
}

term_manager::~term_manager() {
  for (unsigned i = 0; i < OP_LAST; ++ i) {
    delete d_payload_memory[i];
  }
}

std::ostream& operator << (std::ostream& out, const set_tm& stm) {
  output::set_term_manager(out, stm.tm);
  return out;
}

term_ref term_manager::type_of(const term& t) const {
  switch (t.op()) {
  case OP_TYPE_BOOL:
  case OP_TYPE_INTEGER:
  case OP_TYPE_REAL:
    return term_ref();
  case OP_VARIABLE:
    return t[0];
  // Equality
  case OP_EQ:
    return booleanType();
    break;

  // Boolean terms
  case OP_BOOL_CONSTANT:
  case OP_AND:
  case OP_OR:
  case OP_XOR:
  case OP_NOT:
  case OP_IMPLIES:
    return booleanType();
  // Arithmetic terms
  case OP_REAL_CONSTANT:
  case OP_ADD:
  case OP_MUL:
  case OP_SUB:
  case OP_DIV:
    return d_realType;
  default:
    assert(false);
  }
  return term_ref();
}

term_ref term_manager::tcc_of(const term& t) const {
  tcc_map::const_iterator find = d_tcc_map.find(ref_of(t));
  if (find == d_tcc_map.end()) {
    return term_ref();
  } else {
    return find->second;
  }
}

bool term_manager::typecheck(term_ref t_ref) {
  const term& t = term_of(t_ref);

  bool ok = true;

  switch (t.op()) {
  case OP_TYPE_BOOL:
  case OP_TYPE_INTEGER:
  case OP_TYPE_REAL:
  case OP_VARIABLE:
    break;
  // Equality
  case OP_EQ:
    ok = (type_of(t) == type_of(t));
    break;
  // Boolean terms
  case OP_BOOL_CONSTANT:
    break;
  case OP_AND:
  case OP_OR:
  case OP_XOR:
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
  case OP_NOT:
    if (t.size() != 1) {
      ok = false;
    } else {
      ok = type_of(t[0]) == booleanType();
    }
    break;
  case OP_IMPLIES:
    if (t.size() != 2) {
      ok = false;
    } else {
      ok = type_of(t[0]) == booleanType() && type_of(t[1]) == booleanType();
    }
    break;
  // Arithmetic terms
  case OP_REAL_CONSTANT:
    break;
  case OP_ADD:
  case OP_MUL:
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
  case OP_SUB:
    if (t.size() != 2) {
      ok = false;
    } else {
      ok = type_of(t[0]) == realType() && type_of(t[1]) == realType();
    }
    break;
  case OP_DIV:
    if (t.size() != 2) {
      ok = false;
    } else {
      ok = type_of(t[0]) == realType() && type_of(t[1]) == realType();
      // TODO: make TCC
    }
    break;
  default:
    assert(false);
  }

  return ok;
}

}
}
