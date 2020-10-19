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

#include <iosfwd>

namespace sally {

namespace expr {
  class term_manager;
  class term_manager_internal;
}

namespace output {

enum language {
  // Sally/SMTLIB2 (Default)
  MCMT = 0,
  // nuXmv
  NUXMV,
  // Horn clause/SMT2
  HORN,
  // CSV: MCMT for terms, CSV for traces
  MCMT_TAB,
  // Unknown
  UNKNOWN
};

/** Get the string representation of the language */
std::string language_to_string(language lang);

/** Get the language from its string representation */
language language_from_string(std::string lang);

/** Get the term manager associated with out */
expr::term_manager* get_term_manager(std::ostream& out);

/** Set the term manager associated with out */
void set_term_manager(std::ostream& out, expr::term_manager* tm);

/** Get the output language associated with out */
language get_output_language(std::ostream& out);

/** Set the output language associated with out */
void set_output_language(std::ostream& out, language lang);

/** Get the verbosity of the output */
size_t get_verbosity(std::ostream& out);

/** Set the verbosity */
void set_verbosity(std::ostream& out, size_t verbosity);

/** Set the trace stream */
void set_trace_stream(std::ostream& out);

/** Get the trace stream */
std::ostream& get_trace_stream();

/** Set the message stream */
void set_msg_stream(std::ostream& out);

/** Get the message stream */
std::ostream& get_msg_stream(bool show_time);

/** Enable trace for given tag */
void trace_tag_enable(std::string tag);

/** Enable trace for given tag */
void trace_tag_disable(std::string tag);

/** True if the trace tag is enabled */
bool trace_tag_is_enabled(std::string tag);

/** Return the trace stream that outputs anything only if the tag has been enabled */
std::ostream& get_trace(std::string tag);

/** Use let's when printing */
void set_use_lets(std::ostream& out, bool flag);

/** Do we use let's when printing */
bool get_use_lets(std::ostream& out);

}
}
