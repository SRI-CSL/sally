/*
 * output.cpp
 *
 *  Created on: Oct 3, 2014
 *      Author: dejan
 */

#include "utils/output.h"

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

const term::term_manager* get_term_manager(std::ostream& out) {
  return (term::term_manager*) __get_term_manager(out);
}

void set_term_manager(std::ostream& out, const term::term_manager* tm) {
  __get_term_manager(out) = (void*) tm;
}

language get_output_language(std::ostream& out) {
  return (language) __get_output_language(out);
}

void set_term_manager(std::ostream& out, language lang) {
  __get_output_language(out) = lang;
}

}
}
