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

#include "utils/exception.h"
#include "utils/output.h"

#include <iostream>

namespace sally {

exception::exception(expr::term_manager* tm) {
  output::set_term_manager(d_msg, tm);
}

exception::exception(expr::term_manager& tm) {
  output::set_term_manager(d_msg, &tm);
}

exception::exception(const exception& e) {
  e.to_stream(d_msg);
}

void exception::to_stream(std::ostream& out) const {
  out << d_msg.str();
}

std::ostream& operator << (std::ostream& out, const exception& e) {
  e.to_stream(out);
  return out;
}

}

