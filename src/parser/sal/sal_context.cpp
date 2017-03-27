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

#include "parser/sal/sal_context.h"
#include "parser/parser.h"


namespace sally {
namespace parser {
namespace sal {

context::context(expr::term_manager& tm, std::string name)
: d_tm(tm)
, d_name(name)
, d_parameters("parameters")
, d_modules("modules")
, d_constants("constants")
, d_types("types")
{
}

void context::add_parameter(std::string name, expr::term_ref var) {
  if (d_parameters.has_entry(name)) {
    throw parser_exception(name + " already declared");
  }
  d_parameters.add_entry(name, var);
}

void context::add_module(std::string name, sal::module::ref m) {
  if (d_modules.has_entry(name)) {
    throw parser_exception(name + " already declared");
  }
  d_modules.add_entry(name, m);
}

void context::add_assertion(std::string id, assertion_form form, sal::module::ref m, expr::term_ref a) {
  d_assertions.push_back(assertion(id, form, m, a));
}

}
}
}



