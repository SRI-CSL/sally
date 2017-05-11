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

#pragma once

#include "expr/term.h"
#include "expr/term_manager.h"
#include "utils/symbol_table.h"
#include "parser/sal/sal_module.h"
#include "command/command.h"
#include "command/sequence.h"
#include "system/context.h"

#include <iosfwd>

namespace sally {
namespace parser {
namespace sal {

/** Types of model-checking obligations */
enum assertion_form {
  SAL_OBLIGATION,
  SAL_CLAIM,
  SAL_LEMMA,
  SAL_THEOREM
};

class context {

  /** The term manager */
  expr::term_manager& d_tm;

  /** Context name */
  std::string d_name;

  /** Symbol table of parameters */
  utils::symbol_table<expr::term_ref> d_parameters;

  /** Symbol table of modules */
  utils::symbol_table<module::ref> d_modules;

  struct assertion {

    std::string name;
    assertion_form form;
    sal::module::ref m;
    expr::term_ref formula;

    assertion(std::string name, assertion_form form, sal::module::ref m, expr::term_ref formula)
    : name(name), form(form), m(m), formula(formula) {}
  };

  /** List of added assertions */
  std::vector<assertion> d_assertions;

  struct constant {
    std::string name;
    expr::term_ref var;
    expr::term_ref type;
    constant(std::string name, expr::term_ref var, expr::term_ref type)
    : name(name), var(var), type(type) {}
  };

  /** List of added constants */
  std::vector<constant> d_constants;

  struct type {
    std::string name;
    expr::term_ref t;
    type(std::string name, expr::term_ref t)
    : name(name), t(t) {}
  };

  /** List of added types */
  std::vector<type> d_types;

  struct function {
    std::string name;
    expr::term_ref f;
    expr::term_ref f_def;
    function(std::string name, expr::term_ref f, expr::term_ref f_def)
    : name(name), f(f), f_def(f_def) {}
  };

  /** List of defined functions */
  std::vector<function> d_functions;

  /** Temp: substitution map */
  typedef std::map<sal::module::ref, expr::term_manager::substitution_map> module_to_subst_map;
  module_to_subst_map d_SAL_to_Sally_subst;

  /** Temp: map from modules to their state types */
  typedef std::map<sal::module::ref, const system::state_type*> module_to_state_type_map;
  module_to_state_type_map d_state_type;

  /** Process the given module and add commands to the sequence command */
  void process_module(module::ref module, cmd::sequence* seq);

  /** Process the given assertion and add to the sequence command */
  void process_assertion(const system::context& sally_context, const assertion& a, cmd::sequence* seq);

public:

  context(expr::term_manager& tm, std::string name);
  ~context();

  /** Add a parameter to the context */
  void add_parameter(std::string name, expr::term_ref var);

  /** Add a module to the context */
  void add_module(std::string name, sal::module::ref m);

  /** Add a named assertion to the context */
  void add_assertion(std::string id, assertion_form form, sal::module::ref m, expr::term_ref a);

  /** Add a new named constant (variable that stays constant) */
  void add_constant(std::string id, expr::term_ref var, expr::term_ref type);

  /** Add a new named type */
  void add_type(std::string id, expr::term_ref type);

  /** Add a new defined function */
  void add_function(std::string id, expr::term_ref f, expr::term_ref f_def);

  /** Adds definitions to the sally context and return a sequence command to discharge the assertions */
  cmd::command* to_sally_commands(const system::context& sally_context);

};

std::ostream& operator << (std::ostream& out, assertion_form form);

}
}
}
