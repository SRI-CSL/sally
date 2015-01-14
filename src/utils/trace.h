/*
 * trace.h
 *
 *  Created on: Dec 16, 2014
 *      Author: dejan
 */

#pragma once

#include "utils/output.h"

//
// ONLY TO BE USED IN IMPLEMENTATION, NOT IN HEADER FILES
//

#ifdef NDEBUG
#define TRACE(tag) if (false) std::cerr
#else
#define TRACE(tag) if (sal2::output::trace_tag_is_enabled(tag)) sal2::output::get_trace_stream()
#endif
