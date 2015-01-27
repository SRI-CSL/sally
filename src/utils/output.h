/*
 * output.h
 *
 *  Created on: Oct 3, 2014
 *      Author: dejan
 */

#pragma once

#include <iosfwd>

namespace sal2 {

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
  // Unknown
  UNKNOWN
};

/** Get the string representation of the language */
std::string language_to_string(language lang);

/** Get the language from its string representation */
language language_from_string(std::string lang);

/** Get the term manager associated with out */
const expr::term_manager_internal* get_term_manager(std::ostream& out);

/** Set the term manager associated with out */
void set_term_manager(std::ostream& out, const expr::term_manager* tm);

/** Set the term manager associated with out */
void set_term_manager(std::ostream& out, const expr::term_manager_internal* tm);

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

/** Enable trace for given tag */
void trace_tag_enable(std::string tag);

/** Enable trace for given tag */
void trace_tag_disable(std::string tag);

/** True if the trace tag is enabled */
bool trace_tag_is_enabled(std::string tag);

/** Return the trace stream that outputs anything only if the tag has been enabled */
std::ostream& get_trace(std::string tag);

}
}
