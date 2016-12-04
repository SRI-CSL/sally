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

  /** Symbol table of constants */
  utils::symbol_table<expr::term_ref> d_constants;

  /** Symbol table of types */
  utils::symbol_table<expr::term_ref> d_types;

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

public:

  context(expr::term_manager& tm, std::string name);
  ~context();

  void add_parameter(std::string name, expr::term_ref var);

  void add_module(std::string name, sal::module::ref m);

  void add_assertion(std::string id, assertion_form form, sal::module::ref m, expr::term_ref a);

};

}
}
}
