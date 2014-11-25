/*
 * bmc_engine.h
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#include "smt/solver.h"
#include "system/context.h"
#include "engine/engine.h"
#include "expr/term.h"

#include <vector>

namespace sal2 {
namespace bmc {

struct bmc_engine_info {
  static void setup_options(boost::program_options::options_description& options);
  static std::string get_id() { return "bmc_engine"; }
  static engine* new_instance(const system::context& ctx);
};

class bmc_engine : public engine {

  /** SMT solver we're using */
  smt::solver* d_solver;

  /** The type of the state variables */
  expr::term_ref d_state_type;

  /** Unrolling state variables */
  std::vector<expr::term_ref_strong> d_state_variables;

  /** Returns state variabels for state k */
  expr::term_ref state_variables(unsigned k, expr::term_ref type);

  /** Replace the variabels in f from 'from' to 'to' */
  expr::term_ref replace_vars(expr::term_ref f, expr::term_ref from, expr::term_ref to);

public:

  bmc_engine(const system::context& ctx);
  ~bmc_engine();

  /** Query */
  result query(const system::transition_system& ts, const system::state_formula* sf);

};

}
}
