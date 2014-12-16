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
#define TRACE(tag) false &&
#else
#define TRACE(tag) sal2::output::get_trace(tag)
#endif
