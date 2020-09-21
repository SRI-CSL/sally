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

#include <string>
#include <ctime>
#include <iostream>
#include <boost/unordered_set.hpp>

#include "utils/output.h"
#include "utils/exception.h"
#include "expr/term_manager.h"


namespace sally {
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

static
long& __get_use_lets(std::ostream& out) {
  static const int x_index = std::ios_base::xalloc();
  return out.iword(x_index);
}

expr::term_manager* get_term_manager(std::ostream& out) {
  return (expr::term_manager*) __get_term_manager(out);
}

void set_term_manager(std::ostream& out, expr::term_manager* tm) {
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

void set_use_lets(std::ostream& out, bool flag) {
  __get_use_lets(out) = flag;
}

bool get_use_lets(std::ostream& out) {
  return __get_use_lets(out);
}

static
boost::unordered_set<std::string> trace_tags;

void trace_tag_enable(std::string tag) {
  trace_tags.insert(tag);
}

void trace_tag_disable(std::string tag) {
  trace_tags.erase(tag);
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

static
std::ostream* msg_stream = 0;

void set_msg_stream(std::ostream& out) {
  msg_stream = &out;
}

std::ostream& get_msg_stream(bool show_time) {
  std::ostream* result;
  if (trace_stream == 0) {
    result = &std::cout;
  } else {
    result = trace_stream;
  }

  if (show_time) {
    char buf[80];
    time_t now = time(0);
#ifdef __MINGW32__
    struct tm *tstruct = localtime(&now);
    strftime(buf, sizeof(buf), "[%Y-%m-%d.%X] ", tstruct);
#else
    struct tm tstruct;
    localtime_r(&now, &tstruct);
    strftime(buf, sizeof(buf), "[%Y-%m-%d.%X] ", &tstruct);
#endif
    *result << buf;
  }

  return *result;
}

std::string language_to_string(language lang) {
  switch (lang) {
  case MCMT: return "mcmt";
  case NUXMV: return "nuxmv";
  case HORN: return "horn";
  default:
    return "unknown";
  }
}

language language_from_string(std::string lang) {
  if (lang == "mcmt") return MCMT;
  if (lang == "nuxmv") return NUXMV;
  if (lang == "horn") return HORN;
  throw exception(std::string("Unsupported language: ") + lang);
  return UNKNOWN;
}

}
}
