/*
 * output.cpp
 *
 *  Created on: Oct 3, 2014
 *      Author: dejan
 */

#include <string>
#include <iostream>
#include <boost/unordered_set.hpp>

#include "utils/output.h"
#include "expr/term_manager.h"


namespace sal2 {
namespace output {

static
void*& __get_term_manager(std::ostream& out) {
  static const int xindex = std::ios_base::xalloc();
  return out.pword(xindex);
}

static
long& __get_output_language(std::ostream& out) {
  static const int x_index = std::ios_base::xalloc();
  return out.iword(x_index);
}

static
long& __get_verbosity(std::ostream& out) {
  static const int x_index = std::ios_base::xalloc();
  return out.iword(x_index);
}

const expr::term_manager_internal* get_term_manager(std::ostream& out) {
  return (expr::term_manager_internal*) __get_term_manager(out);
}

void set_term_manager(std::ostream& out, const expr::term_manager* tm) {
  __get_term_manager(out) = (void*) const_cast<expr::term_manager*>(tm)->get_internal();
}

void set_term_manager(std::ostream& out, const expr::term_manager_internal* tm) {
  __get_term_manager(out) = (void*) tm;
}

language get_output_language(std::ostream& out) {
  return (language) __get_output_language(out);
}

void set_output_language(std::ostream& out, language lang) {
  __get_output_language(out) = lang;
}

size_t get_verbosity(std::ostream& out) {
  return __get_verbosity(out);
}

void set_verbosity(std::ostream& out, size_t verbosity) {
  __get_verbosity(out) = verbosity;
}

static
boost::unordered_set<std::string> trace_tags;

void trace_tag_enable(std::string tag) {
  trace_tags.insert(tag);
}

bool trace_tag_is_enabled(std::string tag) {
  return trace_tags.find(tag) != trace_tags.end();
}

static
std::ostream* trace_stream = 0;

/** Null stream that ignores everything */
class null_streambuf : public std::streambuf {
public:
  int overflow(int c) {
    return c;
  }
};

class null_stream {
  null_streambuf buf;
  std::ostream stream;
public:
  null_stream(): stream(&buf) {}
  std::ostream& get() { return stream; }
};

static
null_stream null;

std::ostream& get_trace(std::string tag) {
  if (trace_tag_is_enabled(tag)) {
    return get_trace_stream();
  } else {
    return null.get();
  }
}

void set_trace_stream(std::ostream& out) {
  trace_stream = &out;
}

std::ostream& get_trace_stream() {
  if (trace_stream == 0) {
    return std::cerr;
  } else {
    return *trace_stream;
  }
}

}
}
