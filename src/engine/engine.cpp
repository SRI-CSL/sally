/*
 * engine.cpp
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#include "engine/engine.h"

#include <iostream>

namespace sal2 {

engine::engine(const system::context& ctx)
: d_ctx(ctx)
{}

const system::context& engine::ctx() const {
  return d_ctx;
}

expr::term_manager& engine::tm() const {
  return ctx().tm();
}

std::ostream& operator << (std::ostream& out, engine::result result) {

  switch (result) {
  case engine::VALID:
    out << "valid"; break;
  case engine::INVALID:
    out << "invalid"; break;
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
