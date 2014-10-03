/*
 * otuput.h
 *
 *  Created on: Oct 3, 2014
 *      Author: dejan
 */

#include <iostream>

namespace sal2 {
namespace output {

enum output_language {
  // SMTLIB (Default)
  SMTLIB = 0
};

get_ostream_term_manager(std::ostream& out) {
  static const int xindex = std::ios_base::xalloc();
  return out.pword(xindex);
}

static
long& get_ostream_output_language(std::ostream& out) {
  static const int x_index = std::ios_base::xalloc();
  return out.iword(x_index);
}


}
}
