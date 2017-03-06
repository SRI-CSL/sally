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

#include "utils/output.h"

#include <iostream>

//
// ONLY TO BE USED IN IMPLEMENTATION, NOT IN HEADER FILES
//

#ifdef NDEBUG
#define TRACE(tag) if (false) std::cerr
#else
#define TRACE(tag) if (sally::output::trace_tag_is_enabled(tag)) sally::output::get_trace_stream()
#endif

#define MSG(verbosity) if (sally::output::get_verbosity(sally::output::get_msg_stream(false)) >= verbosity) sally::output::get_msg_stream(true)
