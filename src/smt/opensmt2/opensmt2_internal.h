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

#ifdef WITH_OPENSMT2

#include "expr/term_manager.h"
#include "utils/options.h"
#include "smt/solver.h"
#include <opensmt/opensmt2.h>

namespace sally {
namespace smt {

class opensmt2_internal {
public:
    /** Constructor */
    opensmt2_internal(expr::term_manager & tm, const options & opts);

    void add(expr::term_ref ref, solver::formula_class f_class);

    /** Returns the instance id */
    size_t instance() const { return d_instance; }

    solver::result check();

    void push();

    void pop();


private:
    MainSolver & get_main_solver() { return osmt->getMainSolver(); }

    Logic & get_logic() { return osmt->getLogic(); }

    LRALogic & get_lralogic() { return osmt->getLRALogic(); }

    PTRef sally_to_osmt(sally::expr::term_ref ref);

    PTRef mk_osmt_term(expr::term_op op, size_t n, std::vector<PTRef> children);

    size_t d_instance;

    sstat d_last_check_status;

    expr::term_manager& d_tm;

    Opensmt * osmt;
};

}
}

#endif // WITH_OPENSMT2