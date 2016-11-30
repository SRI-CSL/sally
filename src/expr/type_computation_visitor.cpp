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

#include <cassert>

namespace sally {
namespace expr {

void type_computation_visitor::error(expr::term_ref t_ref) const {
  std::stringstream ss;
  expr::term_manager* tm = output::get_term_manager(std::cerr);
  if (tm->get_internal() == &d_tm) {
    output::set_term_manager(ss, tm);
  }
  ss << "Can't typecheck " << t_ref << ".";
  throw exception(ss.str());
}

expr::term_ref type_computation_visitor::type_of(expr::term_ref t_ref) const {
  term_to_term_map::const_iterator find = d_type_cache.find(t_ref);
  if (find == d_type_cache.end()) {
    error(t_ref);
  }
  return find->second;
}

const term& type_computation_visitor::term_of(expr::term_ref t_ref) const {
  return d_tm.term_of(t_ref);
}

type_computation_visitor::type_computation_visitor(expr::term_manager_internal& tm, term_to_term_map& type_cache)
: d_tm(tm)
, d_type_cache(type_cache)
, d_ok(true)
{}

void type_computation_visitor::get_children(expr::term_ref t, std::vector<expr::term_ref>& children) {
  const expr::term& t_term = d_tm.term_of(t);
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
    d_ok = t.size() == 0;
    if (d_ok) t_type = d_tm.type_type();
    break;
  case VARIABLE:
    // Type is first child
    d_ok = t.size() == 1;
    if (d_ok) t_type = t[0];
    break;
  case VARIABLE_BOUND:
    // Type is first child
    d_ok = t.size() == 1;
    if (d_ok) t_type = t[0];
    break;
  case TYPE_BITVECTOR:
    d_ok = t.size() == 0 && d_tm.payload_of<size_t>(t) > 0;
    if (d_ok) t_type = d_tm.type_type();
    break;
  case TYPE_FUNCTION:
  case TYPE_ARRAY:
  case TYPE_TUPLE: {
    d_ok = t.size() > 1;
    if (d_ok) {
      const term_ref* it = t.begin();
      for (; d_ok && it != t.end(); ++ it) {
        d_ok = d_tm.is_type(*it);
      }
    }
    if (d_ok) t_type = d_tm.type_type();
    break;
  }
  case TYPE_PREDICATE_SUBTYPE:
    d_ok = t.size() == 2;
    if (d_ok) {
      term_ref arg = t[0];
      const term& arg_t = term_of(arg);
      if (arg_t.op() != VARIABLE_BOUND) {
        d_ok = false;
      } else {
        term_ref body = t[1];
        if (type_of(body) != d_tm.boolean_type()) {
          d_ok = false;
        } else {
          std::vector<term_ref> vars;
          d_tm.get_bound_variables(body, vars);
          if (vars.size() != 1) {
            d_ok = false;
          } else if (arg != vars[0]) {
            d_ok = false;
          } else {
            // All OK
            t_type = d_tm.type_type();
          }
        }
      }
    }
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
          d_ok = d_tm.is_type(*it);
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
    d_ok = t.size() == 0;
    if (d_ok) t_type = d_tm.boolean_type();
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
    d_ok = t.size() == 0;
    if (d_ok) t_type = d_tm.real_type();
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
      if (d_ok) t_type = t0;
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
  case TERM_BV_SGN_EXTEND:
    if (t.size() != 1) {
      d_ok = false;
    } else {
      term_ref t0 = type_of(t[0]);
      if (!d_tm.is_bitvector_type(t0)) {
        d_ok = false;
      } else {
        size_t child_size = d_tm.bitvector_type_size(t0);
        const bitvector_sgn_extend extend = d_tm.payload_of<
            bitvector_sgn_extend>(t);
        d_ok = extend.size > 0;
        if (d_ok) t_type = d_tm.bitvector_type(child_size + extend.size);
      }
    }
    break;
  case TERM_ARRAY_READ:
    if (t.size() != 2) {
      d_ok = false;
    } else {
      term_ref arr_type = type_of(t[0]);
      if (!d_tm.is_array_type(arr_type)) {
        d_ok = false;
      } else {
        term_ref index_type = d_tm.get_array_type_index(arr_type);
        term_ref element_type = d_tm.get_array_type_element(arr_type);
        if (type_of(t[1]) != index_type) {
          d_ok = false;
        } else {
          t_type = element_type;
        }
      }
    }
    break;
  case TERM_ARRAY_WRITE:
    if (t.size() != 3) {
      d_ok = false;
    } else {
      term_ref arr_type = type_of(t[0]);
      if (!d_tm.is_array_type(arr_type)) {
        d_ok = false;
      } else {
        term_ref index_type = d_tm.get_array_type_index(arr_type);
        term_ref element_type = d_tm.get_array_type_element(arr_type);
        if (type_of(t[1]) != index_type) {
          d_ok = false;
        } else if (type_of(t[2]) != element_type) {
          d_ok = false;
        } else {
          t_type = arr_type;
        }
      }
    }
    break;
  case TERM_TUPLE_CONSTRUCT:
    if (t.size() < 2) {
      d_ok = false;
    } else {
      std::vector<term_ref> children_types;
      for (size_t i = 0; i < t.size(); ++ i) {
        children_types.push_back(type_of(t[i]));
      }
      t_type = d_tm.tuple_type(children_types);
    }
    break;
  case TERM_TUPLE_ACCESS:
    if (t.size() != 1) {
      d_ok = false;
    } else {
      term_ref tuple = t[0];
      term_ref tuple_type = type_of(tuple);
      if (!d_tm.is_tuple_type(tuple_type)) {
        d_ok = false;
      } else {
        size_t access_index = d_tm.payload_of<size_t>(t);
        if (access_index >= term_of(tuple_type).size()) {
          d_ok = false;
        } else {
          t_type = d_tm.get_tuple_type_element(tuple_type, access_index);
        }
      }
    }
    break;
  case TERM_TUPLE_WRITE:
    if (t.size() != 2) {
      d_ok = false;
    } else {
      term_ref tuple = t[0];
      term_ref tuple_type = type_of(tuple);
      if (!d_tm.is_tuple_type(tuple_type)) {
        d_ok = false;
      } else {
        size_t access_index = d_tm.payload_of<size_t>(t);
        if (access_index >= term_of(tuple_type).size()) {
          d_ok = false;
        } else {
          term_ref tuple_element_type = d_tm.get_tuple_type_element(tuple_type, access_index);
          term_ref write_element_type = type_of(t[1]);
          if (tuple_element_type != write_element_type) {
            d_ok = false;
          } else {
            t_type = tuple_type;
          }
        }
      }
    }
    break;
  case TERM_LAMBDA:
    if (t.size() < 2) {
      d_ok = false;
    } else {
      size_t n_args = t.size()-1;
      term_ref body = t[t.size()-1];
      term_ref body_type = type_of(body);
      // Get the variables
      std::vector<term_ref> bound_vars;
      d_tm.get_bound_variables(body, bound_vars);
      if (bound_vars.size() != n_args) {
        d_ok = false;
      } else {
        std::vector<term_ref> arg_types;
        for (size_t i = 0; d_ok && i < n_args; ++ i) {
          if (term_of(t[i]).op() != VARIABLE_BOUND) {
            d_ok = false;
          } else if (t[i] != bound_vars[i]) {
            d_ok = false;
          } else if (i != d_tm.payload_of<size_t>(t[i])) {
            d_ok = false;
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
    }
    break;
  case TERM_EXISTS:
  case TERM_FORALL:
    if (t.size() < 2) {
      d_ok = false;
    } else {
      size_t n_args = t.size()-1;
      term_ref body = t[t.size()-1];
      term_ref body_type = type_of(body);
      if (body_type != d_tm.boolean_type()) {
        d_ok = false;
      } else {
        // Get the variables
        std::vector<term_ref> arg_types;
        size_t prev_index = 0;
        for (size_t i = 0; d_ok && i < n_args; ++i) {
          if (term_of(t[i]).op() != VARIABLE_BOUND) {
            d_ok = false;
          } else {
            size_t index = d_tm.payload_of<size_t>(t[i]);
            if (i && prev_index + 1 != index) {
              d_ok = false;
            } else {
              prev_index = index;
              arg_types.push_back(type_of(t[i]));
            }
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
    } else {
      term_ref f = t[0];
      term_ref f_type = type_of(f);
      if (!d_tm.is_function_type(f_type)) {
        d_ok = false;
      } else {
        // t has extea for function, f_type has extra for co-domain
        if (t.size() != term_of(f_type).size()) {
          d_ok = false;
        } else {
          std::vector<term_ref> arg_types;
          for (size_t i = 0; d_ok && (i + 1 < t.size()); ++ i) {
            term_ref arg_type = type_of(t[i+1]);
            term_ref f_arg_type = d_tm.get_function_type_domain(f_type, i);
            if (arg_type != f_arg_type) {
              d_ok = false;
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


}
}
