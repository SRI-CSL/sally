/*
 * bmc_engine.h
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#include "engine/engine.h"

namespace sal2 {
namespace bmc {

struct bmc_engine_info {
  static void add_options(boost::program_options::options_description& options);
  static std::string get_id() { return "bmc_engine"; }
  static engine* new_instance();
};

class bmc_engine : public engine, public engine_info_static<bmc_engine_info> {

public:

  bmc_engine();
  ~bmc_engine();

  /** Query */
  result query(const system::transition_system& ts, const system::state_formula* sf);

};

}
}
