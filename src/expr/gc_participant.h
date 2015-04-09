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

};

}
}
