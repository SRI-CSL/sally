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

#include "expr/type_computation_visitor.h"
#include "expr/term_manager_internal.h"
#include "expr/term_manager.h"
#include "utils/trace.h"
#include "utils/exception.h"

#include <string>
#include <cassert>

namespace sally {
namespace expr {

void type_computation_visitor::error(term_ref t_ref, std::string message) const {
  std::stringstream ss;
  term_manager* tm = output::get_term_manager(std::cerr);
  if (tm->get_internal() == &d_tm) {
    output::set_term_manager(ss, tm);
  }
  ss << "Can't typecheck " << t_ref;
  if (message.length() > 0) { ss << " (" << message << ")"; }
  ss << ".";
  throw exception(ss.str());
}

term_ref type_computation_visitor::type_of(term_ref t_ref) const {
  term_ref type = d_tm.type_of_if_exists(t_ref);
  if (type.is_null()) {
    error(t_ref, "");
  }
  return type;
}

term_ref type_computation_visitor::base_type_of(term_ref t_ref) const {
  term_ref type = d_tm.base_type_of_if_exists(t_ref);
  if (type.is_null()) {
    error(t_ref, "");
  }
  return type;
}

const term& type_computation_visitor::term_of(term_ref t_ref) const {
  return d_tm.term_of(t_ref);
}

bool type_computation_visitor::compatible(term_ref t1, term_ref t2) const {
  if (t1 == t2) return true;
  return base_type_of(t1) == base_type_of(t2);
}

type_computation_visitor::type_computation_visitor(term_manager_internal& tm, term_to_term_map& type_cache, term_to_term_map& base_type_cache)
: d_tm(tm)
, d_type_cache(type_cache)
, d_base_type_cache(base_type_cache)
, d_ok(true)
{}

void type_computation_visitor::get_children(term_ref t, std::vector<term_ref>& children) {
  const term& t_term = d_tm.term_of(t);
  for (size_t i = 0; i < t_term.size(); ++ i) {
    children.push_back(t_term[i]);
  }
}

visitor_match_result type_computation_visitor::match(term_ref t) {
  if (d_type_cache.find(t) == d_type_cache.end()) {
    // Visit the children if needed and then the node
    return VISIT_AND_CONTINUE;
  } else {
    // Don't visit children or this node or the node
    return DONT_VISIT_AND_BREAK;
  }
}

void type_computation_visitor::visit(term_ref t_ref) {

  term_ref t_type;
  term_ref t_base_type;

  std::stringstream error_message;

  TRACE("types") << "compute_type::visit(" << t_ref << ")" << std::endl;

  // If typechecking failed, we just skip
  if (!d_ok) {
    return;
  }

  // The term we're typechecking (safe, since all subtypes already computed)
  const term& t = term_of(t_ref);
  term_op op = t.op();

  switch (op) {
  // Types -> TYPE_TYPE, with base type for compund types
  case TYPE_TYPE:
  case TYPE_BOOL:
  case TYPE_INTEGER:
  case TYPE_REAL:
  case TYPE_STRING:
    d_ok = t.size() == 0;
    if (d_ok) t_type = d_tm.type_type();
    else error_message << "unexpected children of " << op;
    break;
  case VARIABLE:
    // Type is first child
    d_ok = t.size() > 0;
    if (d_ok) {
      t_type = t[0];
      const term& t_type_term = term_of(t_type);
      if (t_type_term.op() == TYPE_STRUCT) {
        d_ok = t_type_term.size()/2 + 1 == t.size();
        if (!d_ok) error_message << "expecting children to match the struct";
      } else {
        d_ok = t.size() == 1;
        if (!d_ok) error_message << "expecting exactly on child";
      }
    } else error_message << "expecting at least one child";
    break;
  case TYPE_BITVECTOR:
    d_ok = t.size() == 0 && d_tm.payload_of<size_t>(t) > 0;
    if (d_ok) t_type = d_tm.type_type();
    else error_message << "bit-vector type should have non-zero bit size";
    break;
  case TYPE_FUNCTION:
  case TYPE_ARRAY:
  case TYPE_TUPLE: {
    d_ok = t.size() > 1;
    if (!d_ok) error_message << "must have at least 2 arguments for " << op;
    bool base_eq = true;
    if (d_ok) {
      const term_ref* it = t.begin();
      for (; d_ok && it != t.end(); ++ it) {
        d_ok = d_tm.is_type(*it);
        if (d_ok && base_type_of(*it) != *it) {
          base_eq = false;
        } else {
          error_message << "argument " << (it - t.begin()) << " of " << op << " is not a type";
        }
      }
    }
    if (d_ok) {
      t_type = d_tm.type_type();
      if (base_eq) { t_base_type = t_type; }
      else {
        const term_ref* it = t.begin();
        std::vector<term_ref> children;
        for (; it != t.end(); ++ it) {
          children.push_back(base_type_of(*it));
        }
        switch(t.op()) {
        case TYPE_FUNCTION: t_base_type = d_tm.function_type(children); break;
        case TYPE_ARRAY: t_base_type = d_tm.array_type(children[0], children[1]); break;
        case TYPE_TUPLE: t_base_type = d_tm.tuple_type(children); break;
        default:
          assert(false);
        }
      }
    }
    break;
  }
  case TYPE_RECORD: {
    d_ok = t.size() > 0;
    if (!d_ok) error_message << "must have a least 2 arguments for " << op;
    else {
      d_ok = t.size() % 2 == 0;
      if (!d_ok) error_message << "must have even number of arguments for " << op;
      else {
        bool base_eq = true;
        for (size_t i = 0; d_ok && i < t.size(); i += 2) {
          term_ref id = t[i];
          term_ref type = t[i+1];
          if (d_tm.term_of(id).op() != CONST_STRING) {
            d_ok = false;
            error_message << "even children must be field names (string), child " << i << " is not";
          } else if (!d_tm.is_type(type)) {
            d_ok = false;
            error_message << "odd children must be types, child " << i+1 << " is not";
          } else {
            if (base_type_of(type) != type) { base_eq = false; }
          }
        }
        if (d_ok) {
          t_type = d_tm.type_type();
          if (base_eq) { t_base_type = t_type; }
          else {
            term_manager_internal::id_to_term_map fields;
            for (size_t i = 0; i < t.size(); i += 2) {
              std::string id = d_tm.payload_of<utils::string>(t[i]);
              term_ref type = base_type_of(t[i+1]);
              fields[id] = type;
            }
            t_base_type = d_tm.record_type(fields);
          }
        }
      }
    }
    break;
  }
  case TYPE_ENUM: {
    d_ok = t.size() > 1;
    if (d_ok) {
      for (size_t i = 0; d_ok && i < t.size(); ++ i) {
        d_ok = term_of(t[i]).op() == CONST_STRING;
        if (!d_ok) error_message << "enumerations can only have string elements";
      }
      if (d_ok) {
        t_type = d_tm.type_type();
      }
    }
    break;
  }
  case TYPE_PREDICATE_SUBTYPE:
    d_ok = t.size() == 2;
    if (!d_ok) error_message << "must have exactly 2 children";
    if (d_ok) {
      term_ref arg = t[0];
      const term& arg_t = term_of(arg);
      if (arg_t.op() != VARIABLE) {
        d_ok = false;
        error_message << "must have 1st children be a variable";
      } else {
        term_ref body = t[1];
        if (type_of(body) != d_tm.boolean_type()) {
          d_ok = false;
          error_message << "must be of Boolean type";
        } else {
          std::set<term_ref> vars;
          d_tm.get_variables(body, vars);
          if (vars.size() == 0) {
            d_ok = false;
            error_message << "body must have at least one variable";
          } else if (vars.count(arg) == 0) {
            d_ok = false;
            error_message << "argument doen't appear in the body";
          } else {
            // All OK
            t_type = d_tm.type_type();
            t_base_type = base_type_of(arg);
          }
        }
      }
    }
    break;
  case TYPE_STRUCT: {
    if (t.size() % 2) {
      d_ok = false;
      error_message << "must have even number of children";
    } else {
      const term_ref* it = t.begin();
      bool base_eq = true;
      for (bool even = true; d_ok && it != t.end(); even = !even, ++ it) {
        if (even) {
          d_ok = term_of(*it).op() == CONST_STRING;
          if (!d_ok) error_message << "even elements must be strings";
        } else {
          d_ok = d_tm.is_type(*it);
          if (!d_ok) error_message << "odd elements must be types";
          if (base_type_of(*it) != *it) {
            base_eq = false;
          }
        }
      }
      if (d_ok) {
        t_type = d_tm.type_type();
        if (base_eq) { t_base_type = t_type; }
        else {
          std::vector<term_ref> children;
          const term_ref* it = t.begin();
          for (; it != t.end(); ++ it) {
            children.push_back(base_type_of(*it));
          }
          t_base_type = d_tm.mk_term<TYPE_STRUCT>(children.begin(), children.end());
        }
      }
    }
    break;
  }
  // Equality
  case TERM_EQ: {
    if (t.size() != 2) {
      d_ok = false;
      error_message << "must have two children";
    } else {
      d_ok = compatible(type_of(t[0]), type_of(t[1]));
      if (!d_ok) error_message << "lhs and rhs types are not compatible";
    }
    if (d_ok) t_type = d_tm.boolean_type();
    break;
  }
  // ITE
  case TERM_ITE:
    if (t.size() != 3) {
      d_ok = false;
      error_message << "must have 3 children";
    } else {
      term_ref t0 = type_of(t[0]);
      term_ref t1 = type_of(t[1]);
      term_ref t2 = type_of(t[2]);
      d_ok = t0 == d_tm.boolean_type() && compatible(t1, t2);
      if (!d_ok) error_message << "incompatible children types";
      if (d_ok) {
        if (t1 == t2) t_type = t1;
        else {
          t_type = base_type_of(t1);
          if (!d_tm.is_primitive_type(t_type)) {
            // We don't allow ITEs on non-primitive types, e.g.
            //  a: int -> real
            //  b: real -> int
            // The type of ITE(c, a, b) is too much work
            d_ok = false;
            error_message << "branches must be of primitive types";
          }
        }
      }
    }
    break;
  // Boolean terms
  case CONST_BOOL:
    d_ok = t.size() == 0;
    if (d_ok) t_type = d_tm.boolean_type();
    else error_message << "no children allowed";
    break;
  case TERM_AND:
  case TERM_OR:
  case TERM_XOR:
    if (t.size() < 2) {
      d_ok = false;
      error_message << "must have at least 2 children";
    } else {
      for (const term_ref* it = t.begin(); d_ok && it != t.end(); ++ it) {
        if (type_of(*it) != d_tm.boolean_type()) {
          d_ok = false;
          error_message << "children must be Boolean";
          break;
        }
      }
    }
    if (d_ok) t_type = d_tm.boolean_type();
    break;
  case TERM_NOT:
    if (t.size() != 1) {
      d_ok = false;
      error_message << "only 1 child allowed";
    } else {
      d_ok = type_of(t[0]) == d_tm.boolean_type();
      if (d_ok) error_message << "child must be Boolean";
    }
    if (d_ok) t_type = d_tm.boolean_type();
    break;
  case TERM_IMPLIES:
    if (t.size() != 2) {
      d_ok = false;
      error_message << "only 2 children allowed";
    } else {
      d_ok = type_of(t[0]) == d_tm.boolean_type() && type_of(t[1]) == d_tm.boolean_type();
      if (!d_ok) error_message << "children must be Boolean";
    }
    if (d_ok) t_type = d_tm.boolean_type();
    break;
  // Arithmetic terms
  case CONST_RATIONAL:
    d_ok = t.size() == 0;
    if (!d_ok) error_message << "no children allowed";
    if (d_ok) {
      if (d_tm.payload_of<rational>(t).is_integer()) {
        t_type = d_tm.integer_type();
      } else {
        t_type = d_tm.real_type();
      }
    }
    break;
  case TERM_ADD:
  case TERM_MUL:
    if (t.size() < 2) {
      d_ok = false;
      error_message << "must have at least 2 children";
    } else {
      bool is_int = true;
      for (const term_ref* it = t.begin(); d_ok && it != t.end(); ++ it) {
        term_ref it_type = type_of(*it);
        is_int = is_int && d_tm.is_integer_type(it_type);
        if (base_type_of(it_type) != d_tm.real_type()) {
          d_ok = false;
          error_message << "children must be real or integer";
          break;
        }
      }
      if (d_ok) {
        if (is_int) {
          t_type = d_tm.integer_type();
        } else {
          t_type = d_tm.real_type();
        }
      }
    }
    break;
  case TERM_SUB:
    // 1 child is OK
    if (t.size() == 1) {
      d_ok = base_type_of(t[0]) == d_tm.real_type();
      if (!d_ok) error_message << "child must be real or integer";
      if (d_ok) {
        if (d_tm.is_integer_type(type_of(t[0]))) {
          t_type = d_tm.integer_type();
        } else {
          t_type = d_tm.real_type();
        }
      }
    } else if (t.size() != 2) {
      d_ok = false;
      error_message << "must have 1 or 2 children";
    } else {
      d_ok = base_type_of(t[0]) == d_tm.real_type() && base_type_of(t[1]) == d_tm.real_type();
      error_message << "children must be real or integer";
      if (d_ok) {
        if (d_tm.is_integer_type(type_of(t[0])) && d_tm.is_integer_type(type_of(t[1]))) {
          t_type = d_tm.integer_type();
        } else {
          t_type = d_tm.real_type();
        }
      }
    }
    break;
  case TERM_LEQ:
  case TERM_LT:
  case TERM_GEQ:
  case TERM_GT:
    if (t.size() != 2) {
      d_ok = false;
      error_message << "must have 2 children";
    } else {
      d_ok = base_type_of(t[0]) == d_tm.real_type() && base_type_of(t[1]) == d_tm.real_type();
      if (d_ok) t_type = d_tm.boolean_type();
      else error_message << "children must be real or integer";
    }
    break;
  case TERM_IS_INT:
    if (t.size() != 1) {
      d_ok = false;
      error_message << "must have 1 child";
    } else {
      d_ok = base_type_of(t[0]) == d_tm.real_type();
      if (d_ok) t_type = d_tm.boolean_type();
      else error_message << "child must be real";
    }
    break;
  case TERM_TO_INT:
    if (t.size() != 1) {
      d_ok = false;
      error_message << "must have 1 child";
    } else {
      d_ok = type_of(t[0]) == d_tm.real_type();
      if (d_ok) t_type = d_tm.integer_type();
      else error_message << "child must be real";
    }
    break;
  case TERM_TO_REAL:
    if (t.size() != 1) {
      d_ok = false;
      error_message << "must have 1 child";
    } else {
      d_ok = type_of(t[0]) == d_tm.integer_type();
      if (d_ok) t_type = d_tm.real_type();
      else error_message << "child must be integer";
    }
    break;
  case TERM_DIV:
  case TERM_MOD:
    if (t.size() != 2) {
      d_ok = false;
      error_message << "must have 2 children";
    } else {
      d_ok = base_type_of(t[0]) == d_tm.real_type() && base_type_of(t[1]) == d_tm.real_type();
      if (d_ok) t_type = d_tm.real_type();
      else error_message << "children must be real or integer";
    }
    break;
  // Bitvector terms
  case CONST_BITVECTOR: {
    d_ok = t.size() == 0;
    if (!d_ok) error_message << "no children allowed";
    else {
      size_t size = d_tm.payload_of<bitvector>(t_ref).size();
      t_type = d_tm.bitvector_type(size);
    }
    break;
  }
  case TERM_BV_NOT:
    if (t.size() != 1) {
      d_ok = false;
      error_message << "must have 1 child";
    } else {
      term_ref t0 = base_type_of(t[0]);
      d_ok = d_tm.is_bitvector_type(t0);
      if (d_ok) t_type = t0;
      else error_message << "child must be a bit-vector";
    }
    break;
  case TERM_BV_SUB:
    if (t.size() == 1) {
      term_ref t0 = base_type_of(t[0]);
      d_ok = d_tm.is_bitvector_type(t0);
      if (d_ok) t_type = t0;
      else error_message << "child must be a bit-vector";
    } else if (t.size() == 2) {
      term_ref t0 = base_type_of(t[0]);
      term_ref t1 = base_type_of(t[1]);
      if (!d_tm.is_bitvector_type(t0)) {
        d_ok = false;
        error_message << "1st child must be a bit-vector";
      } else {
        d_ok = t0 == t1;
        if (!d_ok) error_message << "children not compatible";
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
      error_message << "must have at least 2 children";
    } else {
      const term_ref* it = t.begin();
      term_ref t0 = base_type_of(*it);
      if (!d_tm.is_bitvector_type(t0)) {
        d_ok = false;
        error_message << "1st child must be a bit-vector";
      } else {
        for (++ it; d_ok && it != t.end(); ++ it) {
          if (type_of(*it) != t0) {
            d_ok = false;
            error_message << "child " << (it - t.begin()) << " is not compatible";
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
      error_message << "must have 2 children";
    } else {
      term_ref t0 = type_of(t[0]);
      if (!d_tm.is_bitvector_type(t0)) {
        d_ok = false;
        error_message << "1st child must be bit-vector";
      } else {
        d_ok = t0 == type_of(t[1]);
        if (!d_ok) error_message << "2nd child is not compatible";
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
      error_message << "must have 2 children";
    } else {
      term_ref t0 = type_of(t[0]);
      if (!d_tm.is_bitvector_type(t0)) {
        d_ok = false;
        error_message << "1st child must be bit-vector";
      } else {
        d_ok = t0 == type_of(t[1]);
        if (!d_ok) error_message << "2nd child not compatible";
      }
      if (d_ok) t_type = d_tm.boolean_type();
    }
    break;
  case TERM_BV_CONCAT:
    if (t.size() < 2) {
      d_ok = false;
      error_message << "must have at least 2 children";
    } else {
      for (const term_ref* it = t.begin(); d_ok && it != t.end(); ++ it) {
        if (!d_tm.is_bitvector_type(type_of(*it))) {
          d_ok = false;
          error_message << "child " << (it - t.begin()) << " must be bit-vector";
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
      error_message << "must have 1 child";
    } else {
      term_ref t0 = type_of(t[0]);
      if (!d_tm.is_bitvector_type(t0)) {
        d_ok = false;
        error_message << "child must be bit-vector";
      } else {
        size_t child_size = d_tm.bitvector_type_size(t0);
        const bitvector_extract& extract = d_tm.payload_of<bitvector_extract>(t);
        if (extract.high < extract.low) {
          d_ok = false;
          error_message << extract.high << " < " << extract.low;
        } else {
          d_ok = extract.high < child_size;
          if (d_ok) {
            size_t size = extract.high - extract.low + 1;
            t_type = d_tm.bitvector_type(size);
          } else {
            error_message << "high bit exceeds bit width";
          }
        }
      }
    }
    break;
  case TERM_BV_SGN_EXTEND:
    if (t.size() != 1) {
      d_ok = false;
      error_message << "must have 1 child";
    } else {
      term_ref t0 = type_of(t[0]);
      if (!d_tm.is_bitvector_type(t0)) {
        d_ok = false;
        error_message << "child must be bit-vector";
      } else {
        size_t child_size = d_tm.bitvector_type_size(t0);
        const bitvector_sgn_extend extend = d_tm.payload_of<bitvector_sgn_extend>(t);
        d_ok = extend.size > 0;
        if (!d_ok) error_message << "extend size must be positive";
        if (d_ok) t_type = d_tm.bitvector_type(child_size + extend.size);
      }
    }
    break;
  case TERM_ARRAY_READ:
    if (t.size() != 2) {
      d_ok = false;
      error_message << "must have 2 children";
    } else {
      term_ref arr_type = type_of(t[0]);
      if (!d_tm.is_array_type(arr_type)) {
        d_ok = false;
        error_message << "1st child must be array";
      } else {
        term_ref index_type = d_tm.get_array_type_index(arr_type);
        term_ref element_type = d_tm.get_array_type_element(arr_type);
        if (d_tm.base_type_of(t[1]) != d_tm.base_type_of(index_type)) {
          d_ok = false;
          error_message << "index type not compatible";
        } else {
          t_type = element_type;
        }
      }
    }
    break;
  case TERM_ARRAY_WRITE:
    if (t.size() != 3) {
      d_ok = false;
      error_message << "must have 3 children";
    } else {
      term_ref arr_type = type_of(t[0]);
      if (!d_tm.is_array_type(arr_type)) {
        d_ok = false;
        error_message << "1st child must be array";
      } else {
        term_ref index_type = d_tm.get_array_type_index(arr_type);
        term_ref element_type = d_tm.get_array_type_element(arr_type);
        if (d_tm.base_type_of(t[1]) != d_tm.base_type_of(index_type)) {
          d_ok = false;
          error_message << "index type not compatible";
        } else if (d_tm.base_type_of(t[2]) != d_tm.base_type_of(element_type)) {
          d_ok = false;
          error_message << "element and write type not compatible";
        } else {
          t_type = arr_type;
        }
      }
    }
    break;
  case TERM_ARRAY_LAMBDA:
    d_ok = t.size() == 2;
    if (!d_ok) error_message << "must have exactly 2 children";
    if (d_ok) {
      term_ref arg = t[0];
      const term& arg_t = term_of(arg);
      if (arg_t.op() != VARIABLE) {
        d_ok = false;
        error_message << "must have 1st children be a variable";
      } else {
        // All OK
        term_ref index_type = type_of(arg);
        term_ref body_type = type_of(t[1]);
        t_type = d_tm.array_type(index_type, body_type);
      }
    }
    break;
  case TERM_TUPLE_CONSTRUCT:
    if (t.size() < 2) {
      d_ok = false;
      error_message << "must have at least 2 children";
    } else {
      std::vector<term_ref> children_types;
      for (size_t i = 0; i < t.size(); ++ i) {
        children_types.push_back(type_of(t[i]));
      }
      t_type = d_tm.tuple_type(children_types);
    }
    break;
  case TERM_TUPLE_READ:
    if (t.size() != 1) {
      d_ok = false;
      error_message << "must have 1 child";
    } else {
      term_ref tuple = t[0];
      term_ref tuple_type = type_of(tuple);
      if (!d_tm.is_tuple_type(tuple_type)) {
        d_ok = false;
        error_message << "child 1 must be a tuple";
      } else {
        size_t access_index = d_tm.payload_of<size_t>(t);
        if (access_index >= term_of(tuple_type).size()) {
          d_ok = false;
          error_message << "index out of bounds";
        } else {
          t_type = d_tm.get_tuple_type_element(tuple_type, access_index);
        }
      }
    }
    break;
  case TERM_TUPLE_WRITE:
    if (t.size() != 2) {
      d_ok = false;
      error_message << "must have 2 children";
    } else {
      term_ref tuple = t[0];
      term_ref tuple_type = type_of(tuple);
      if (!d_tm.is_tuple_type(tuple_type)) {
        d_ok = false;
        error_message << "child 1 must be a tuple";
      } else {
        size_t access_index = d_tm.payload_of<size_t>(t);
        if (access_index >= term_of(tuple_type).size()) {
          d_ok = false;
          error_message << "index out of bounds";
        } else {
          term_ref tuple_element_type = d_tm.get_tuple_type_element(tuple_type, access_index);
          term_ref write_element_type = type_of(t[1]);
          if (!compatible(tuple_element_type, write_element_type)) {
            d_ok = false;
            error_message << "write types not compatible";
          } else {
            t_type = tuple_type;
          }
        }
      }
    }
    break;
  case TERM_RECORD_CONSTRUCT:
    if (t.size() == 0) {
      d_ok = false;
      error_message << "must have at least 2 children";
    } else if (t.size() % 2 == 1) {
      d_ok = false;
      error_message << "must have even number of children";
    } else {
      term_manager_internal::id_to_term_map fields;
      for (size_t i = 0; d_ok && i < t.size(); i += 2) {
        if (term_of(t[i]).op() != CONST_STRING) {
          d_ok = false;
          error_message << "even children must be field id's, " << i << " is not";
        } else {
          std::string field = d_tm.payload_of<utils::string>(t[i]);
          fields[field] = type_of(t[i+1]);
        }
      }
      if (d_ok) {
        t_type = d_tm.record_type(fields);
      }
    }
    break;
  case TERM_RECORD_READ:
    if (t.size() != 2) {
      d_ok = false;
      error_message << "must have 2 children";
    } else {
      term_ref rec = t[0];
      term_ref rec_type = type_of(rec);
      term_ref rec_field = t[1];
      if (!d_tm.is_record_type(rec_type)) {
        d_ok = false;
        error_message << "child 1 must be a record";
      } else {
        const term& rec_field_term = term_of(rec_field);
        if (rec_field_term.op() != CONST_STRING) {
          d_ok = false;
          error_message << "the read field must be a string";
        } else {
          std::string field = d_tm.payload_of<utils::string>(rec_field_term);
          term_ref field_type = d_tm.get_record_type_field_type(rec_type, field);
          if (field_type.is_null()) {
            d_ok = false;
            error_message << "field not part of the record type";
          } else {
            t_type = field_type;
          }
        }
      }
    }
    break;
  case TERM_RECORD_WRITE:
    if (t.size() != 3) {
      d_ok = false;
      error_message << "must have 3 children";
    } else {
      term_ref rec = t[0];
      term_ref rec_type = type_of(rec);
      term_ref rec_field = t[1];
      term_ref value = t[2];
      term_ref value_type = type_of(value);
      if (!d_tm.is_record_type(rec_type)) {
        d_ok = false;
        error_message << "child 1 must be a record";
      } else {
        const term& rec_field_term = term_of(rec_field);
        if (rec_field_term.op() != CONST_STRING) {
          d_ok = false;
          error_message << "the read field must be a string";
        } else {
          std::string field = d_tm.payload_of<utils::string>(rec_field_term);
          term_ref field_type = d_tm.get_record_type_field_type(rec_type, field);
          if (field_type.is_null()) {
            d_ok = false;
            error_message << "field not part of the record type";
          } else {
            if (!d_tm.compatible(field_type, value_type)) {
              d_ok = false;
              error_message << "value not compatible with the field type";
            } else {
              t_type = rec_type;
            }
          }
        }
      }
    }
    break;
  case CONST_ENUM:
    if (t.size() != 1) {
      d_ok = false;
      error_message << "must have exactly 1 child";
    } else {
      const term& enum_type = term_of(t[0]);
      size_t i = d_tm.payload_of<size_t>(t);
      if (i >= enum_type.size()) {
        d_ok = false;
        error_message << "enum index out of bounds";
      } else {
        d_ok = true;
        t_type = t[0];
      }
    }
    break;
  case TERM_LAMBDA:
    if (t.size() < 2) {
      d_ok = false;
      error_message << "must have at least 2 children";
    } else {
      size_t n_args = t.size()-1;
      term_ref body = t[t.size()-1];
      term_ref body_type = type_of(body);
      // Get the variables
      std::set<term_ref> free_vars;
      d_tm.get_variables(body, free_vars);
      std::vector<term_ref> arg_types;
      for (size_t i = 0; d_ok && i < n_args; ++ i) {
        if (term_of(t[i]).op() != VARIABLE) {
          d_ok = false;
          error_message << "argument " << i << " is not a variable";
// REMOVED: too strict
//        } else if (free_vars.count(t[i]) == 0) {
//          d_ok = false;
//          error_message << "argument " << i << " does not appear in the body";
        } else {
          arg_types.push_back(type_of(t[i]));
        }
      }
      if (d_ok) {
        // (x1, ..., xn) -> body_type
        arg_types.push_back(body_type);
        t_type = d_tm.function_type(arg_types);
      }
    }
    break;
  case TERM_EXISTS:
  case TERM_FORALL:
    if (t.size() < 2) {
      d_ok = false;
      error_message << "must have 2 children";
    } else {
      size_t n_args = t.size()-1;
      term_ref body = t[t.size()-1];
      term_ref body_type = type_of(body);
      if (body_type != d_tm.boolean_type()) {
        d_ok = false;
        error_message << "body must be Boolean";
      } else {
        // Get the variables
        std::set<term_ref> free_vars;
        d_tm.get_variables(body, free_vars);
        std::vector<term_ref> arg_types;
        for (size_t i = 0; d_ok && i < n_args; ++i) {
          if (term_of(t[i]).op() != VARIABLE) {
            d_ok = false;
            error_message << "argument " << i << " is not a variable";
// TOO STRICT
//          } else if (free_vars.count(t[i]) == 0) {
//            d_ok = false;
//            error_message << "argument " << i << " does not appear in the body";
          } else {
            arg_types.push_back(type_of(t[i]));
          }
        }
        if (d_ok) {
          t_type = d_tm.boolean_type();
        }
      }
    }
    break;
  case TERM_FUN_APP: {
    if (t.size() < 2) {
      d_ok = false;
      error_message << "must have at least 2 arguments";
    } else {
      term_ref f = t[0];
      term_ref f_type = type_of(f);
      if (!d_tm.is_function_type(f_type)) {
        d_ok = false;
        error_message << "1st child must be a function";
      } else {
        // t has extra for function, f_type has extra for co-domain
        if (t.size() != term_of(f_type).size()) {
          d_ok = false;
          error_message << "argument mismatch: expected " << t.size() - 1 << " got " << term_of(f_type).size();
        } else {
          std::vector<term_ref> arg_types;
          for (size_t i = 0; d_ok && (i + 1 < t.size()); ++ i) {
            term_ref arg_type = type_of(t[i+1]);
            term_ref f_arg_type = d_tm.get_function_type_domain(f_type, i);
            if (d_tm.base_type_of(arg_type) != d_tm.base_type_of(f_arg_type)) {
              d_ok = false;
              error_message << "argument " << i << " type mismatch";
            }
          }
          if (d_ok) {
            t_type = d_tm.get_function_type_codomain(f_type);
          }
        }
      }
    }
    break;
  }
  case CONST_STRING:
    d_ok = t.size() == 0;
    if (d_ok) t_type = d_tm.string_type();
    else error_message << "no children allowed";
    break;
  default:
    assert(false);
  }

  TRACE("types") << "compute_type::visit(" << t_ref << ") => " << t_type << std::endl;

  assert(!d_ok || !t_type.is_null());
  assert(!d_tm.is_type(t) || d_tm.is_primitive_type(t) || !t_base_type.is_null());

  if (!d_ok) {
    error(t_ref, error_message.str());
  } else {
    assert(d_type_cache.find(t_ref) == d_type_cache.end());
    d_type_cache[t_ref] = t_type;
    if (d_tm.is_type(t) && !d_tm.is_primitive_type(t)) {
      d_base_type_cache[t_ref] = t_base_type;
    }
  }
}


}
}
