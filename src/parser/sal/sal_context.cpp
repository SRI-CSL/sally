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

namespace sally {
namespace parser {
namespace sal {

context::context(expr::term_manager& tm)
: d_tm(tm)
, d_modules("modules")
, d_constants("constants")
, d_types("types")
{
  // Add the basic types
  d_types.add_entry("REAL", d_tm.real_type());
  d_types.add_entry("INTEGER", d_tm.integer_type());
  d_types.add_entry("BOOLEAN", d_tm.boolean_type());
}

}
}
}



