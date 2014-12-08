/*
 * factory.cpp
 *
 *  Created on: Nov 25, 2014
 *      Author: dejan
 */

#include "engine/factory.h"
#include "utils/exception.h"
#include "utils/module_setup.h"

#include <vector>
#include <map>

namespace sal2 {

/** Type for setting up individual engines */
class engine_data : public module_data<engine, system::context> {
public:
  engine_data();
};

/** Map from id's to engine information */
static engine_data s_engine_data;

engine* factory::mk_engine(std::string id, const system::context& ctx) {
  return s_engine_data.get_module_info(id).new_instance(ctx);
}

void factory::setup_options(boost::program_options::options_description& options) {
  for (engine_data::const_iterator it = s_engine_data.data().begin(); it != s_engine_data.data().end(); ++ it) {
    std::stringstream ss;
    ss << "Engine '" << it->second->get_id() << "' options";
    boost::program_options::options_description engine_options(ss.str());
    it->second->setup_options(engine_options);
    if (engine_options.options().size() > 0) {
      options.add(engine_options);
    }
  }
}

void factory::get_engines(std::vector<std::string>& out) {
  for (engine_data::const_iterator it = s_engine_data.data().begin(); it != s_engine_data.data().end(); ++ it) {
    out.push_back(it->second->get_id());
  }
}

}

#include "engine/engines_list.h"
