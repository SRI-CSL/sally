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

#ifdef WITH_MATHSAT5

#include <mathsat.h>

namespace sally {
namespace smt {

/** Yices term hash. */
struct mathsat5_hasher {
  size_t operator() (msat_term value) const { return msat_term_id(value); }
};

/** Equality checks */
struct mathsat5_eq {
  bool operator() (const msat_term& t1, const msat_term& t2) const {
    return msat_term_id(t1) == msat_term_id(t2);
  }
};

}
}

#endif
