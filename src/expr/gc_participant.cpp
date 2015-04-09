/*
 * gc.cpp
 *
 *  Created on: Apr 9, 2015
 *      Author: dejan
 */

#include "expr/gc_participant.h"

namespace sally {
namespace expr {

gc_participant::gc_participant(term_manager& tm)
: d_gc_participant_tm(tm)
{
  d_gc_participant_tm.gc_register(this);
}

gc_participant::~gc_participant()
{
  d_gc_participant_tm.gc_deregister(this);
}

}
}

