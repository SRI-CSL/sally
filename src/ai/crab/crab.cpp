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

#include "crab.h"

#include "utils/trace.h"

#ifdef WITH_CRAB
#include "crab_mcmt/crab_mcmt.hpp"
#endif

namespace sally {
namespace ai {

using namespace crab_mcmt;

crab::crab(const system::context& ctx)
: abstract_interpreter(ctx)
{
  // Construct crab
}

crab::~crab() {
  // Destruct crab
}

void crab::run(const system::transition_system* ts, std::vector<system::state_formula*>& out) {

#ifndef WITH_CRAB
  cerr () << "Warning: no crab found so do nothing\n";
#else  

  // Run the interpreter
  MSG(1) << "Crab: starting" << std::endl;

  // // Initial states
  // expr::term_ref I = ts->get_initial_states();
  // expr::term_ref T = ts->get_transition_relation();

  // TRACE("crab") << "crab: I = " << I << std::endl;
  // TRACE("crab") << "crab: T = " << T << std::endl;

  // // Invariant as a term
  // expr::term_ref invariant_term = I;

  // // State type has all the transition system variables
  // const system::state_type* state_type = ts->get_state_type();

  // MSG(1) << "Crab: done" << std::endl;

  // // Invariant as a state formula
  // system::state_formula* invariant = new system::state_formula(tm(), state_type, invariant_term);
  // out.push_back(invariant);

  
  // TODO: read the abstract domain from program_options
  abs_domain_t dom = q_polka;

  // EXAMPLE of how to build formulas in crab-mcmt
  // TODO: translate from system::transition_system* to crab_mcmt::mcmt_trans_sys 
  ExprFactory efac;    
  Expr x0 = bind::intConst (mkTerm<std::string> ("x", efac));
  Expr y0 = bind::intConst (mkTerm<std::string> ("y", efac));
  Expr x1 = bind::intConst (mkTerm<std::string> ("x.pre", efac));
  Expr y1 = bind::intConst (mkTerm<std::string> ("y.pre", efac));
  Expr x2 = bind::intConst (mkTerm<std::string> ("x.post", efac));
  Expr y2 = bind::intConst (mkTerm<std::string> ("y.post", efac));
  ExprVector initial_vars = {x0, y0};
  ExprVector pre_vars = {x1, y1};
  ExprVector post_vars = {x2, y2};

  Expr initial = mk<AND>(mk<EQ>(x0, mkTerm<mpq_class>(1, efac)),
			 mk<EQ>(y0, mkTerm<mpq_class>(0, efac)));

  Expr step = mk<AND>(mk<EQ>(y1, mk<MINUS>(x2,x1)),
		      mk<EQ>(y1, mk<MINUS>(y2,mkTerm<mpq_class>(1, efac))));

  try {
    // Build a transition system and infer invariants from it
    mcmt_trans_sys t ("t1", initial, step, initial_vars, pre_vars, post_vars);
    MSG(1) << "Before preprocessing mcmt transition system \n" << t << "\n";    
    t.preprocess ();
    MSG(1) << "After preprocessing mcmt transition system \n" << t << "\n";
    abs_domain_opts opts (dom, true /*stats_enabled*/);
    mcmt_ai analyzer (t);
    Expr res = analyzer.infer (opts);
    MSG(1) << "Invariants \n" << res << "\n";
    // TODO: translate back the invariants to a sally term
  } catch (crab_mcmt_exception &e) {
    std::cout << e.what();
  }
  

  
#endif   
}

void crab::gc_collect(const expr::gc_relocator& gc_reloc) {
  // Ignore for now
}

}
}
