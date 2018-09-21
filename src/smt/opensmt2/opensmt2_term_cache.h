//
// Created by Martin Blicha on 21.09.18.
//

#ifndef SALLY_OPENSMT2_TERM_CACHE_H
#define SALLY_OPENSMT2_TERM_CACHE_H

#include <opensmt/PTRef.h>
#include "expr/term_manager.h"
#include "expr/gc_participant.h"
#include "expr/term_map.h"

namespace sally{
namespace smt{


class opensmt2_term_cache{
//    expr::term_manager& d_tm;

    using term_to_opensmt_cache = expr::term_ref_map<PTRef>;

    term_to_opensmt_cache cache;

public:

    /** Create a new cache */
    opensmt2_term_cache();

    /** Set the term cache from t -> PTRef. */
    void set_term_cache(expr::term_ref t, PTRef ptref);

    /** Returns the yices term associated with t, or NULL_TERM otherwise */
    PTRef get_term_cache(expr::term_ref t) const;

};


}
}

#endif //SALLY_OPENSMT2_TERM_CACHE_H
