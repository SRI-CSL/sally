/*
 * otuput.h
 *
 *  Created on: Oct 3, 2014
 *      Author: dejan
 */

#pragma once

#include <iostream>

namespace sal2 {

namespace term {
  class term_manager;
};

namespace output {

enum output_language {
  // SMTLIB (Default)
  SMTLIB = 0
};

/** Get the term manager associated with out */
const term::term_manager* get_term_manager(std::ostream& out);

/** Set the term manager associated with out */
void set_term_manager(std::ostream& out, const term::term_manager* tm);

/** Get the output language associated with out */
output_language get_output_language(std::ostream& out);

/** Set the output language associated with out */
void set_term_manager(std::ostream& out, output_language lang);

}
}
