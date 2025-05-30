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
#include "expr/gc_relocator.h"
#include "expr/bitvector.h"

#include "command/assume.h"
#include "command/declare_state_type.h"
#include "command/define_states.h"
#include "command/define_transition.h"
#include "command/define_transition_system.h"
#include "command/query.h"
#include "command/sequence.h"

#include <cassert>
#include <sstream>
#include <iostream>
#include <unordered_set>

#include "parser/btor2/btor2.h"

#ifdef WITH_BTOR2TOOLS

extern "C"
{
#include "btor2parser.h"
}

namespace sally {
namespace parser {

std::unordered_map<Btor2Tag, expr::term_op> btor2_tag_to_term_op = {
  {BTOR2_TAG_add, expr::TERM_BV_ADD},
  {BTOR2_TAG_and, expr::TERM_BV_AND},
  {BTOR2_TAG_concat, expr::TERM_BV_CONCAT},
  {BTOR2_TAG_eq, expr::TERM_EQ},
  {BTOR2_TAG_iff, expr::TERM_EQ},
  {BTOR2_TAG_implies, expr::TERM_IMPLIES},
  {BTOR2_TAG_ite, expr::TERM_ITE},
  {BTOR2_TAG_mul, expr::TERM_BV_MUL},
  {BTOR2_TAG_nand, expr::TERM_BV_NAND},
  {BTOR2_TAG_neg, expr::TERM_BV_NEG},
  {BTOR2_TAG_nor, expr::TERM_BV_NOR},
  {BTOR2_TAG_not, expr::TERM_BV_NOT},
  {BTOR2_TAG_or, expr::TERM_BV_OR},
  {BTOR2_TAG_read, expr::TERM_ARRAY_READ},
  {BTOR2_TAG_sdiv, expr::TERM_BV_SDIV},
  {BTOR2_TAG_sext, expr::TERM_BV_SGN_EXTEND},
  {BTOR2_TAG_sgt, expr::TERM_BV_SGT},
  {BTOR2_TAG_sgte, expr::TERM_BV_SGEQ},
  {BTOR2_TAG_slice, expr::TERM_BV_EXTRACT},
  {BTOR2_TAG_sll, expr::TERM_BV_SHL},
  {BTOR2_TAG_slt, expr::TERM_BV_SLT},
  {BTOR2_TAG_slte, expr::TERM_BV_SLEQ},
  {BTOR2_TAG_smod, expr::TERM_BV_SMOD},
  {BTOR2_TAG_sra, expr::TERM_BV_ASHR},
  {BTOR2_TAG_srem, expr::TERM_BV_SREM},
  {BTOR2_TAG_srl, expr::TERM_BV_LSHR},
  {BTOR2_TAG_sub, expr::TERM_BV_SUB},
  {BTOR2_TAG_udiv, expr::TERM_BV_UDIV},
  {BTOR2_TAG_ugt, expr::TERM_BV_UGT},
  {BTOR2_TAG_ugte, expr::TERM_BV_UGEQ},
  {BTOR2_TAG_ult, expr::TERM_BV_ULT},
  {BTOR2_TAG_ulte, expr::TERM_BV_ULEQ},
  {BTOR2_TAG_urem, expr::TERM_BV_UREM},
  {BTOR2_TAG_write, expr::TERM_ARRAY_WRITE},
  {BTOR2_TAG_xnor, expr::TERM_BV_XNOR},
  {BTOR2_TAG_xor, expr::TERM_BV_XOR},
};

class btor2_parser : public internal_parser_interface {

  /** The term mangager */
  expr::term_manager& tm;

  /** The context */
  const system::context& ctx;

  /** File we're parsing */
  std::string filename;

  /** Line we're parsing */
  int lineno;

  /** The command we're constructing */
  cmd::command* command;

  // Map from indices to terms
  std::vector<expr::term_ref> nodes;

  // List of variables indices.
  // Input variables are essentially just state variables with no next or init
  // so we can just use the state variables for both.
  std::vector<size_t> state_vars;

  typedef std::map<size_t, size_t> var_to_var_map;

  // Map from variables to their init versions
  var_to_var_map init;

  // Map from variables to their next versions
  var_to_var_map next;

  // List of root nodes
  std::vector<expr::term_ref_strong> bad;
  std::vector<expr::term_ref_strong> constraints;

  /** Bitvector 1 */
  expr::term_ref_strong one;

  /** Bitvector 0 */
  expr::term_ref_strong zero;

  /** Set the term */
  void set_term(size_t index, expr::term_ref term, expr::term_ref type_id);

  /** Add a bitvector type */
  void add_bv_type(size_t id, size_t size);

  /** Add an array type */
  void add_array_type(size_t id, size_t index, size_t element);

  /** Get the sort at index */
  expr::term_ref get_type(size_t index) const;

  /** Get the term at index (negated if negative) */
  expr::term_ref get_term(int index) const;

  /** Get the term at index (negated if negative), casting to bitvector if necessary */
  expr::term_ref get_term_bitvector(int index) const;

  /** Cast boolean term to bitvector term */
  // expr::term_ref bool_to_bitvector(expr::term_ref t);

  /** Get the term at index (negated if negative) with a specific width */
  size_t get_term_width(int index) const;

  /** Add a state variable */
  void add_state_var(size_t id, size_t type_id, std::string name);

  /** Set init term of state var */
  void set_init(size_t id, size_t type_id, size_t var_id, expr::term_ref value);

  /** Set next term of state var */
  void set_next(size_t id, size_t type_id, size_t var_id, expr::term_ref value);

  /** Add a unary term */
  void add_unary_term(size_t id, expr::term_op op, size_t type_id, expr::term_ref t);

  /** Add a binary term */
  void add_binary_term(size_t id, expr::term_op op, size_t type_id, expr::term_ref t1, expr::term_ref t2);

  /** Add a ternary term */
  void add_ternary_term(size_t id, expr::term_op op, size_t type_id, expr::term_ref t1, expr::term_ref t2, expr::term_ref t3);

  /** Build the transition system from the parsed terms */
  void build_transition_system();

public:
  btor2_parser(const system::context& ctx, const char* filename);
  virtual ~btor2_parser();

  cmd::command* parse_command();
  int get_current_parser_line() const;
  int get_current_parser_position() const;
  std::string get_filename() const;
};

void btor2_parser::set_term(size_t index, expr::term_ref term, expr::term_ref type_id) {
  // Ensure size
  if (index >= nodes.size()) {
    nodes.resize((index * 2) + 1);
  }
  nodes[index] = term;
}

void btor2_parser::add_bv_type(size_t id, size_t size) {
  // Ensure size
  if (id >= nodes.size()) {
    nodes.resize((id * 2) + 1);
  }
  // Remember
  nodes[id] = tm.bitvector_type(size);
}

void btor2_parser::add_array_type(size_t id, size_t index, size_t element) {
  // Ensure size
  if (id >= nodes.size()) {
    nodes.resize((id * 2) + 1);
  }
  // Remember
  nodes[id] = tm.array_type(get_type(index), get_type(element));
}

expr::term_ref btor2_parser::get_type(size_t index) const {
  return nodes[index];
}

expr::term_ref btor2_parser::get_term(int index) const {
  size_t i = index >= 0 ? index : -index;
  expr::term_ref result = nodes[i];
  // If the id is negative, negate the term
  if (index >= 0) {
    return result;
  } else {
    return tm.mk_term(expr::TERM_BV_NOT, result);
  }
}

expr::term_ref btor2_parser::get_term_bitvector(int index) const {
  size_t i = index >= 0 ? index : -index;
  expr::term_ref result = nodes[i];

  // If the term is a boolean, convert it to a bitvector
  expr::term_ref type = tm.type_of(result);
  if (tm.is_boolean_type(type)) {
    result = tm.mk_term(expr::TERM_ITE, result, one, zero);
  }

  // If the id is negative, negate the term
  if (index >= 0) {
    return result;
  } else {
    return tm.mk_term(expr::TERM_BV_NOT, result);
  }
}

size_t btor2_parser::get_term_width(int index) const {
  expr::term_ref term = get_term_bitvector(index);
  if (tm.is_bitvector_type(tm.type_of(term))) {
    return tm.get_bitvector_size(term);
  } else {
    throw parser_exception("Term is not a bitvector", filename, lineno);
  }
}

void btor2_parser::add_state_var(size_t id, size_t type_id, std::string name) {
  expr::term_ref type = get_type(type_id);
  expr::term_ref term = tm.mk_variable(name, type);
  set_term(id, term, type);
  state_vars.push_back(id);
}

void btor2_parser::set_init(size_t id, size_t type_id, size_t var_id, expr::term_ref value) {
  var_to_var_map::const_iterator find = init.find(var_id);
  if (find != init.end()) {
    throw parser_exception("Init already defined for this variable.", filename, lineno);
  }
  expr::term_ref type = get_type(type_id);
  init[var_id] = id;
  set_term(id, value, type);
}

void btor2_parser::set_next(size_t id, size_t type_id, size_t var_id, expr::term_ref value) {
  expr::term_ref type = get_type(type_id);
  next[var_id] = id;
  set_term(id, value, type);
}

void btor2_parser::add_unary_term(size_t id, expr::term_op op, size_t type_id, expr::term_ref t) {
  expr::term_ref type = get_type(type_id);
  expr::term_ref term = tm.mk_term(op, t);
  set_term(id, term, type);
}

void btor2_parser::add_binary_term(size_t id, expr::term_op op, size_t type_id, expr::term_ref t1, expr::term_ref t2) {
  expr::term_ref type = get_type(type_id);
  expr::term_ref term = tm.mk_term(op, t1, t2);
  set_term(id, term, type);
}

void btor2_parser::add_ternary_term(size_t id, expr::term_op op, size_t type_id, expr::term_ref t1, expr::term_ref t2, expr::term_ref t3) {
  expr::term_ref type = get_type(type_id);
  expr::term_ref term = tm.mk_term(op, t1, t2, t3);
  set_term(id, term, type);
}

void btor2_parser::build_transition_system() {
  // Construct a dummy input type, need it to construct the state type
  std::vector<std::string> input_names;
  std::vector<expr::term_ref> input_types;
  expr::term_ref input_type_ref = tm.mk_struct_type(input_names, input_types);

  // Create the state type
  std::vector<std::string> state_names;
  std::vector<expr::term_ref> state_types;

  for (size_t i = 0; i < state_vars.size(); ++ i) {
    expr::term_ref var_ref = get_term_bitvector(state_vars[i]);
    const expr::term& var = tm.term_of(var_ref);
    state_names.push_back(tm.get_variable_name(var));
    state_types.push_back(tm.type_of(var));
  }
  expr::term_ref state_type_ref = tm.mk_struct_type(state_names, state_types);

  system::state_type* state_type = new system::state_type("state_type", tm, state_type_ref, input_type_ref);
  cmd::command* state_type_declare = new cmd::declare_state_type("state_type", state_type);

  // Get the state variables
  const std::vector<expr::term_ref>& sally_current_vars = state_type->get_variables(system::state_type::STATE_CURRENT);
  const std::vector<expr::term_ref>& sally_next_vars = state_type->get_variables(system::state_type::STATE_NEXT);

  // Create the conversion table from btor vars to input, state, and next vars
  expr::term_manager::substitution_map btor_to_state_var;
  for (size_t i = 0; i < state_vars.size(); ++ i) {
    expr::term_ref btor_var = get_term_bitvector(state_vars[i]);
    expr::term_ref state_var = sally_current_vars[i];
    btor_to_state_var[btor_var] = state_var;
  }

  // Initialize the registers
  std::vector<expr::term_ref> init_children;
  for (size_t i = 0; i < state_vars.size(); ++ i) {
    expr::term_ref state_var = sally_current_vars[i];
    var_to_var_map::const_iterator find = init.find(state_vars[i]);
    if (find == init.end()) { continue; } 
    expr::term_ref init_value = get_term_bitvector(find->second);
    expr::term_ref eq = tm.mk_term(expr::TERM_EQ, state_var, init_value);
    init_children.push_back(eq);
  }
  expr::term_ref init = tm.mk_and(init_children);
  init = tm.substitute_and_cache(init, btor_to_state_var);
  system::state_formula* init_formula = new system::state_formula(tm, state_type, init);

  // Define the transition relation
  std::vector<expr::term_ref> transition_children;
  for (size_t i = 0; i < state_vars.size(); ++ i) {
    expr::term_ref next_var = sally_next_vars[i];
    var_to_var_map::const_iterator find = next.find(state_vars[i]);
    if (find == next.end()) { continue; } 
    expr::term_ref next_value = get_term_bitvector(find->second);
    expr::term_ref eq = tm.mk_term(expr::TERM_EQ, next_var, next_value);
    transition_children.push_back(eq);
  }
  expr::term_ref transition = tm.mk_and(transition_children);
  transition = tm.substitute_and_cache(transition, btor_to_state_var);
  system::transition_formula* transition_formula = new system::transition_formula(tm, state_type, transition);

  // Define any invariants
  std::vector<expr::term_ref> constraint_children;
  for (size_t i = 0; i < constraints.size(); ++ i) {
    expr::term_ref constraint = constraints[i];
    // FIXME: is this necessary?
    if (tm.type_of(constraint) != tm.boolean_type()) {
      constraint = tm.mk_term(expr::TERM_EQ, constraint, one);
    }
    constraint_children.push_back(constraint);
  }
  expr::term_ref invar = tm.mk_and(constraint_children);
  invar = tm.substitute_and_cache(invar, btor_to_state_var);
  system::state_formula* invar_formula = new system::state_formula(tm, state_type, invar);

  // Define the transition system
  system::transition_system* transition_system = new system::transition_system(state_type, init_formula, transition_formula, invar_formula);
  cmd::command* transition_system_define = new cmd::define_transition_system("Sys", transition_system);

  // Query
  std::vector<expr::term_ref> bad_children;
  for (size_t i = 0; i < bad.size(); ++ i) {
    expr::term_ref bad_term = tm.substitute_and_cache(bad[i], btor_to_state_var);
    if (tm.type_of(bad_term) != tm.boolean_type()) {
      bad_term = tm.mk_term(expr::TERM_EQ, bad_term, one);
    }
    bad_children.push_back(bad_term);
  }
  expr::term_ref property = tm.mk_or(bad_children);
  property = tm.mk_term(expr::TERM_NOT, property);
  system::state_formula* property_formula = new system::state_formula(tm, state_type, property);
  cmd::command* query = new cmd::query(ctx, "Sys", property_formula);

  // Make the final command
  cmd::sequence* full_command = new cmd::sequence();
  full_command->push_back(state_type_declare);
  full_command->push_back(transition_system_define);
  full_command->push_back(query);

  command = full_command;
}

btor2_parser::btor2_parser(const system::context& ctx, const char* filename)
: tm(ctx.tm())
, ctx(ctx)
, filename(filename)
, lineno(0)
, command(0)
{
  one = expr::term_ref_strong(tm, tm.mk_bitvector_constant(expr::bitvector(1, 1)));
  zero = expr::term_ref_strong(tm, tm.mk_bitvector_constant(expr::bitvector(1, 0)));

  Btor2Parser* parser;
  Btor2LineIterator it;
  Btor2Line* line;

  FILE *input_file = fopen(filename, "r");
  if (!input_file) {
    throw parser_exception("Error opening file: " + std::string(filename), filename, lineno);
  }

  parser = btor2parser_new();
  if (!parser) {
    throw parser_exception("Error creating btor2 parser", filename, lineno);
  }
  if (!btor2parser_read_lines(parser, input_file)) {
    const char *err = btor2parser_error(parser);
    throw parser_exception("Error reading btor2 file: " + std::string(err), filename, lineno);
  }

  std::string symbol;
  it = btor2parser_iter_init(parser);
  while ((line = btor2parser_iter_next(&it))) {
    lineno = line->lineno;
    switch (line->tag)
    {
    case BTOR2_TAG_bad: {
      expr::term_ref term = get_term_bitvector(line->args[0]);
      expr::term_ref type = tm.type_of(term);
      bad.push_back(expr::term_ref_strong(tm, term));
      set_term(line->id, term, type);
      break;
    }
    case BTOR2_TAG_constraint: {
      expr::term_ref term = get_term_bitvector(line->args[0]);
      expr::term_ref type = tm.type_of(term);
      constraints.push_back(expr::term_ref_strong(tm, term));
      set_term(line->id, term, type);
      break;
    }
    case BTOR2_TAG_input:
      if (line->symbol == NULL) {
        symbol = "input_" + std::to_string(line->id);
      } else {
        symbol = line->symbol;
      }
      add_state_var(line->id, line->sort.id, symbol);
      break;
    case BTOR2_TAG_state:
      if (line->symbol == NULL) {
        symbol = "state_" + std::to_string(line->id);
      } else {
        symbol = line->symbol;
      }
      add_state_var(line->id, line->sort.id, symbol);
      break;
    case BTOR2_TAG_init:
      set_init(line->id, line->sort.id, line->args[0], get_term_bitvector(line->args[1]));
      break;
    case BTOR2_TAG_next:
      set_next(line->id, line->sort.id, line->args[0], get_term_bitvector(line->args[1]));
      break;
    case BTOR2_TAG_output:
      break;
    case BTOR2_TAG_sort:
      if (line->sort.tag == BTOR2_TAG_SORT_bitvec) {
        add_bv_type(line->id, line->sort.bitvec.width);
      } else {
        add_array_type(line->id, line->sort.array.index, line->sort.array.element);
      }
      break;
    case BTOR2_TAG_one:{
      expr::term_ref type = get_type(line->sort.id);
      size_t width = tm.get_bitvector_type_size(type);
      expr::term_ref term = tm.mk_bitvector_constant(expr::bitvector(width, 1));
      set_term(line->id, term, type);
      break;
    }
    case BTOR2_TAG_ones: {
      expr::term_ref type = get_type(line->sort.id);
      size_t width = tm.get_bitvector_type_size(type);
      expr::term_ref term = tm.mk_bitvector_constant(expr::bitvector::one(width));
      set_term(line->id, term, type);
      break;
    }
    case BTOR2_TAG_zero: {
      expr::term_ref type = get_type(line->sort.id);
      size_t width = tm.get_bitvector_type_size(type);
      expr::term_ref term = tm.mk_bitvector_constant(expr::bitvector(width, 0));
      set_term(line->id, term, type);
      break;
    }
    case BTOR2_TAG_const: {
      expr::term_ref type = get_type(line->sort.id);
      expr::term_ref term = tm.mk_bitvector_constant(expr::bitvector(line->constant, 2, line->sort.bitvec.width));
      set_term(line->id, term, type);
      break;
    }
    case BTOR2_TAG_constd: {
      expr::term_ref type = get_type(line->sort.id);
      expr::term_ref term = tm.mk_bitvector_constant(expr::bitvector(line->constant, 10, line->sort.bitvec.width));
      set_term(line->id, term, type);
      break;
    }
    case BTOR2_TAG_consth: {
      expr::term_ref type = get_type(line->sort.id);
      expr::term_ref term = tm.mk_bitvector_constant(expr::bitvector(line->constant, 16, line->sort.bitvec.width));
      set_term(line->id, term, type);
      break;
    }
    case BTOR2_TAG_neq: {
      expr::term_ref eq = tm.mk_term(expr::TERM_EQ, get_term_bitvector(line->args[0]), get_term_bitvector(line->args[1]));
      add_unary_term(line->id, expr::TERM_NOT, line->sort.id, eq);
      break;
    }
    case BTOR2_TAG_iff:
    case BTOR2_TAG_implies: {
      add_binary_term(line->id, btor2_tag_to_term_op[line->tag], line->sort.id, 
                      get_term(line->args[0]), get_term(line->args[1]));
      break;
    }
    case BTOR2_TAG_eq:      
    case BTOR2_TAG_sgt:
    case BTOR2_TAG_sgte:
    case BTOR2_TAG_slt:
    case BTOR2_TAG_slte:
    case BTOR2_TAG_ugt:
    case BTOR2_TAG_ugte:
    case BTOR2_TAG_ult:
    case BTOR2_TAG_ulte:
    case BTOR2_TAG_and:
    case BTOR2_TAG_add:
    case BTOR2_TAG_concat:
    case BTOR2_TAG_mul:
    case BTOR2_TAG_nand:
    case BTOR2_TAG_nor:
    case BTOR2_TAG_or:
    case BTOR2_TAG_read:
    case BTOR2_TAG_sdiv:
    case BTOR2_TAG_sll:
    case BTOR2_TAG_smod:
    case BTOR2_TAG_sra:
    case BTOR2_TAG_srem:
    case BTOR2_TAG_srl:
    case BTOR2_TAG_sub:
    case BTOR2_TAG_udiv:
    case BTOR2_TAG_urem:
    case BTOR2_TAG_xnor:
    case BTOR2_TAG_xor:
      add_binary_term(line->id, btor2_tag_to_term_op[line->tag], line->sort.id, 
                      get_term_bitvector(line->args[0]), get_term_bitvector(line->args[1]));
      break;
    case BTOR2_TAG_sext: {
      expr::term_ref type = get_type(line->sort.id);
      expr::term_ref term;
      size_t amt = line->args[1];
      if (amt == 0) {
        term = get_term_bitvector(line->args[0]);
      } else {
        expr::bitvector_sgn_extend ext(amt);
        term = tm.mk_bitvector_sgn_extend(get_term_bitvector(line->args[0]), ext);
      }
      set_term(line->id, term, type);
      break;
    }
    case BTOR2_TAG_uext: {
      expr::term_ref type = get_type(line->sort.id);
      expr::term_ref term;
      size_t amt = line->args[1];
      if (amt == 0) {
        term = get_term_bitvector(line->args[0]);
      } else {
        expr::term_ref zero_term = tm.mk_bitvector_constant(expr::bitvector(amt, 0));
        term = tm.mk_term(expr::TERM_BV_CONCAT, zero_term, get_term_bitvector(line->args[0]));
      }
      set_term(line->id, term, type);
      break;
    }
    case BTOR2_TAG_rol: 
    case BTOR2_TAG_ror:
    case BTOR2_TAG_saddo:
    case BTOR2_TAG_smulo:
    case BTOR2_TAG_ssubo:
    case BTOR2_TAG_sdivo:
    case BTOR2_TAG_uaddo:
    case BTOR2_TAG_umulo:
    case BTOR2_TAG_usubo:
      throw parser_exception("Unsupported btor2 tag: " + std::string(line->name), filename, lineno);
    case BTOR2_TAG_inc: {
      size_t width = get_term_width(line->args[0]);
      expr::term_ref one_term = tm.mk_bitvector_constant(expr::bitvector(width, 1));
      add_binary_term(line->id, expr::TERM_BV_ADD, line->sort.id, 
                      get_term_bitvector(line->args[0]), one_term);
      break;
    }
    case BTOR2_TAG_dec: {
      size_t width = get_term_width(line->args[0]);
      expr::term_ref one_term = tm.mk_bitvector_constant(expr::bitvector(width, 1));
      add_binary_term(line->id, expr::TERM_BV_SUB, line->sort.id, 
                      get_term_bitvector(line->args[0]), one_term);
      break;
    }
    case BTOR2_TAG_redand: {
      size_t arg_width = get_term_width(line->args[0]);
      expr::term_ref ones_term = tm.mk_bitvector_constant(expr::bitvector(arg_width, (1 << arg_width) - 1));
      add_binary_term(line->id, expr::TERM_EQ, line->sort.id, get_term_bitvector(line->args[0]), ones_term);
      break;
    }
    case BTOR2_TAG_redor: {
      size_t arg_width = get_term_width(line->args[0]);
      expr::term_ref zeros_term = tm.mk_bitvector_constant(expr::bitvector(arg_width, 0));
      expr::term_ref eq = tm.mk_term(expr::TERM_EQ, get_term_bitvector(line->args[0]), zeros_term);
      add_unary_term(line->id, expr::TERM_NOT, line->sort.id, eq);
      break;
    }
    case BTOR2_TAG_redxor: {
      expr::term_ref term = tm.mk_bitvector_extract(get_term_bitvector(line->args[0]), expr::bitvector_extract(line->sort.bitvec.width - 1, line->sort.bitvec.width - 1));
      for (size_t i = 0; i < line->sort.bitvec.width - 1; ++ i) {
        expr::term_ref next_term = tm.mk_bitvector_extract(get_term_bitvector(line->args[0]), expr::bitvector_extract(i, i));
        term = tm.mk_term(expr::TERM_BV_XOR, term, next_term);
      }
      set_term(line->id, term, get_type(line->sort.id));
      break;
    }
    case BTOR2_TAG_neg:
    case BTOR2_TAG_not:
      add_unary_term(line->id, btor2_tag_to_term_op[line->tag], line->sort.id, get_term_bitvector(line->args[0]));
      break;
    case BTOR2_TAG_slice: {
      expr::term_ref type = get_type(line->sort.id);
      expr::term_ref term = tm.mk_bitvector_extract(get_term_bitvector(line->args[0]), expr::bitvector_extract(line->args[1], line->args[2]));
      set_term(line->id, term, type);
      break;
    }
    case BTOR2_TAG_ite: {
      // cast first arg to bools and then add_ternary_term
      expr::term_ref t1 = get_term_bitvector(line->args[0]);
      expr::term_ref t1_bool = tm.mk_term(expr::TERM_EQ, t1, one);
      add_ternary_term(line->id, btor2_tag_to_term_op[line->tag], line->sort.id, 
                      t1_bool, get_term_bitvector(line->args[1]), get_term_bitvector(line->args[2]));
      break;
    }
    case BTOR2_TAG_write:
      add_ternary_term(line->id, btor2_tag_to_term_op[line->tag], line->sort.id, 
                      get_term_bitvector(line->args[0]), get_term_bitvector(line->args[1]), get_term_bitvector(line->args[2]));
      break;
    case BTOR2_TAG_fair:
      throw parser_exception("Unsupported btor2 tag: fair", filename, lineno);
    case BTOR2_TAG_justice:
      throw parser_exception("Unsupported btor2 tag: justice", filename, lineno);
    default:
      throw parser_exception("Unsupported btor2 tag: " + std::to_string(line->tag), filename, lineno);
    }
  }

  build_transition_system();
  btor2parser_delete(parser);
}

btor2_parser::~btor2_parser()
{  }

cmd::command* btor2_parser::parse_command() {
  // Just return the saved command, and mark it back to 0
  cmd::command* result = command;
  command = 0;
  return result;
}

int btor2_parser::get_current_parser_line() const {
  return 0;
}

int btor2_parser::get_current_parser_position() const {
  return 0;
}

std::string btor2_parser::get_filename() const {
  return filename;
}

internal_parser_interface* new_btor2_parser(const system::context& ctx, const char* filename) {
  return new btor2_parser(ctx, filename);
}

}
}

#endif