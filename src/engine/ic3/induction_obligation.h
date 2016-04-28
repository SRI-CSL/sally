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

#include "expr/term.h"

#include <vector>

namespace sally {
namespace ic3 {

/**
 * An obligation to do at frame k. This is just a carrier, the semantics
 * depend on the context. It could be that we're trying to reach P at
 * frame k. Or, we could be trying to prove P is inductive at frame k.
 */
struct induction_obligation {

  /** The formula thar refutes the counter-example */
  expr::term_ref F_fwd;
  /** The counter-example generalization */
  expr::term_ref F_cex;
  /** Depth to the real counter-example */
  size_t d;
  /** Score of the obligation */
  double score;
  /** How many times has this obligation been refined */
  size_t refined;

  /** Construct the obligation */
  induction_obligation(expr::term_manager& tm, expr::term_ref F_fwd, expr::term_ref F_cex, size_t d, double score, size_t refined = 0);

  /** Compare for equality */
  bool operator == (const induction_obligation& o) const;

  /** Compare the budget values */
  bool operator < (const induction_obligation& o) const;

  /** Bump the internal score (score is capped below at 1) */
  void bump_score(double amount);

};

struct induction_obligation_cmp_better {
  bool operator() (const induction_obligation& ind1, const induction_obligation& ind2) const;
};

struct induction_obligation_cmp_worse {
  induction_obligation_cmp_better cmp_better;
  bool operator() (const induction_obligation& ind1, const induction_obligation& ind2) const {
    return cmp_better(ind2, ind1);
  }
};

std::ostream& operator << (std::ostream& out, const induction_obligation& ind);

}
}
