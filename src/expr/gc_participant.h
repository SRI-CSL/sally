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

#include "expr/term_manager.h"

namespace sally {
namespace expr {

class gc_relocator;

/**
 * An interface class for anyone wanting to participate in term garbage
 * collection.
 */
class gc_participant {

  /** The term manager we're participating in */
  term_manager& d_gc_participant_tm;

  /** Should we deregister when destructed */
  bool d_deregister;

public:

  /** Construct a GC participant */
  gc_participant(term_manager& tm, bool deregister = true);

  /** Destruct a GC participant */
  virtual ~gc_participant();

  /** Called for the participant to collect unused terms and reallocate used terms */
  virtual void gc_collect(const gc_relocator& gc_reloc) = 0;

  /** Returns the term manager */
  term_manager& tm() const;
};

}
}
