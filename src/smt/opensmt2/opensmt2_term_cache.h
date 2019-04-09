//
// Created by Martin Blicha on 21.09.18.
//

#ifndef SALLY_OPENSMT2_TERM_CACHE_H
#define SALLY_OPENSMT2_TERM_CACHE_H

#include <opensmt/PTRef.h>

#include "expr/term_manager.h"
#include "expr/gc_participant.h"
#include "expr/term_map.h"

#include <unordered_map>

namespace sally {
namespace smt {


class opensmt2_term_cache {

  using term_to_opensmt_cache = expr::term_ref_map<PTRef>;
  using opensmt_to_terms_cache = std::unordered_map<PTRef, expr::term_ref, PTRefHash>;

  term_to_opensmt_cache cache;
  opensmt_to_terms_cache cache2;

public:

  /** Create a new cache */
  opensmt2_term_cache();

  /** Set the term cache from t -> PTRef. */
  void set_term_cache(expr::term_ref t, PTRef ptref);

  /** Returns the OpenSMT term associated with t, or PTRef_Undef otherwise */
  PTRef get_term_cache(expr::term_ref t) const;

  /** Set the OpenSMT term cache from PTRef -> t. */
  void set_osmt_term_cache(PTRef ptref, expr::term_ref t);

  /** Returns the Sally term associated with t, or empty term otherwise */
  expr::term_ref get_osmt_term_cache(PTRef ptref) const;

};


}
}

#endif //SALLY_OPENSMT2_TERM_CACHE_H
