/*
 * gc_participant.h
 *
 *  Created on: Apr 9, 2015
 *      Author: dejan
 */

#pragma once

#include "expr/term_manager.h"

namespace sally {
namespace expr {

class gc_info;

/**
 * An interface class for anyone wanting to participate in term garbage
 * collection.
 */
class gc_participant {

  term_manager& d_gc_participant_tm;

public:

  /** Construct a GC participant */
  gc_participant(term_manager& tm);

  /** Destruct a GC participant */
  virtual ~gc_participant();

  /** Called for the participant to collect unused terms and reallocate used terms */
  virtual void gc_collect(const gc_info& gc_reloc) = 0;

};

}
}
