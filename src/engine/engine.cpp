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

#include "engine/engine.h"
#include "utils/output.h"

#include <iostream>

namespace sally {

engine::engine(const system::context& ctx)
: gc_participant(ctx.tm())
, d_ctx(ctx)
{}

const system::context& engine::ctx() const {
  return d_ctx;
}

expr::term_manager& engine::tm() const {
  return ctx().tm();
}

std::ostream& operator << (std::ostream& out, engine::result result) {

  output::language lang = output::get_output_language(out);

  switch (result) {
  case engine::VALID:
    if (lang == output::HORN) {
      out << "sat";
    } else {
      out << "valid";
    }
    break;
  case engine::INVALID:
    if (lang == output::HORN) {
      out << "unsat";
    } else {
      out << "invalid";
    }
    break;
  case engine::UNKNOWN:
    out << "unknown"; break;
  case engine::INTERRUPTED:
    out << "interrupted"; break;
  case engine::UNSUPPORTED:
    out << "unsupported"; break;
  case engine::SILENT:
    out << "silent"; break;
  default:
    out << "unknown";
  }
#undef SWITCH_TO_STRING
  return out;
}

}

