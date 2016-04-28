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

#include "induction_obligation.h"

namespace sally {
namespace ic3 {

bool induction_obligation_cmp_better::operator() (const induction_obligation& ind1, const induction_obligation& ind2) const {
  // Prefer sahllow ones
  if (ind1.d != ind2.d) {
    return ind1.d < ind2.d;
  }
  // Prefer higher scores
  if (ind1.score != ind2.score) {
    return ind1.score > ind2.score;
  }
  // Otherwise just break ties, basically term id's => created earlier wins
  if (ind1.F_cex != ind2.F_cex) {
    return ind1.F_cex < ind2.F_cex;
  }
  return ind1.F_fwd < ind2.F_fwd;
}

induction_obligation::induction_obligation(expr::term_manager& tm, expr::term_ref F_fwd, expr::term_ref F_cex, size_t d, double score, size_t refined)
: F_fwd(F_fwd)
, F_cex(F_cex)
, d(d)
, score(score)
, refined(refined)
{}

bool induction_obligation::operator == (const induction_obligation& o) const {
  return F_cex == o.F_cex && F_fwd == o.F_fwd;
}

void induction_obligation::bump_score(double amount) {
  if (score + amount >= 0) {
    score += amount;
  } else {
    score = 0;
  }
}

bool induction_obligation::operator < (const induction_obligation& o) const {
  if (F_cex == o.F_cex) {
    return F_fwd < o.F_fwd;
  }
  return F_cex < o.F_cex;
}

std::ostream& operator << (std::ostream& out, const induction_obligation& ind) {
  out << ind.F_fwd;
  return out;
}
}
}
