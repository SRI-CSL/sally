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
#include "opensmt2_term_cache.h"
#include <opensmt/opensmt2.h>

namespace sally {
namespace smt {

class opensmt2_internal {
public:
    /** Constructor */
    opensmt2_internal(expr::term_manager & tm, const options & opts);

    ~opensmt2_internal() {
      delete d_osmt;
    }

    void add(expr::term_ref ref, solver::formula_class f_class);

    /** Returns the instance id */
    size_t instance() const { return d_instance; }

    solver::result check();

    void push();

    void pop();

    expr::model::ref get_model();

    void add_variable(expr::term_ref var, solver::variable_class f_class);

    void interpolate(std::vector<expr::term_ref> & out);


private:

    static unsigned int s_instance_id;

    MainSolver & get_main_solver() { return d_osmt->getMainSolver(); }

    Logic & get_logic() { return d_osmt->getLogic(); }

    LRALogic & get_lralogic() { return d_osmt->getLRALogic(); }

    PTRef sally_to_osmt(sally::expr::term_ref ref);

    sally::expr::term_ref osmt_to_sally(PTRef ref);

    PTRef mk_osmt_term(expr::term_op op, size_t n, const vector<PTRef> &children);

    std::vector<expr::term_ref> d_variables;

    expr::term_manager& d_tm;

    size_t d_instance;

    sstat d_last_check_status;

    Opensmt * d_osmt;

    opensmt2_term_cache d_term_cache;

    unsigned int d_stack_level = 0;

    std::vector<std::vector<unsigned int>> d_stacked_A_partitions;

    unsigned int d_current_partition = 0;

    ipartitions_t get_A_mask() const;
};

}
}

#endif // WITH_OPENSMT2
