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

class context {

  /** The term manager */
  expr::term_manager& d_tm;

  /** Symbol table of modules */
  utils::symbol_table<module::ref> d_modules;

  /** Symbol table of constants */
  utils::symbol_table<expr::term_ref> d_constants;

  /** Symbol table of types */
  utils::symbol_table<expr::term_ref> d_types;

public:

  context(expr::term_manager& tm);
  ~context();

};

}
}
}
