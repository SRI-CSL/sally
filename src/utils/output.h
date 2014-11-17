/*
 * otuput.h
 *
 *  Created on: Oct 3, 2014
 *      Author: dejan
 */

#pragma once

#include <iostream>

namespace sal2 {

namespace expr {
  class term_manager;
  class term_manager_internal;
}

namespace output {

enum language {
  // SMTLIB (Default)
  SMTLIB = 0
};

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

}
}
