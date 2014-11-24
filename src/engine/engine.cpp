/*
 * engine.cpp
 *
 *  Created on: Nov 23, 2014
 *      Author: dejan
 */

#include "engine/engine.h"
#include "engine/bmc/bmc_engine.h"
#include "utils/exception.h"

#include <vector>
#include <map>

using namespace sal2;
using namespace boost::program_options;


struct engine_info_dynamic {
  virtual void add_options(options_description& options) const = 0;
  virtual std::string get_id() const = 0;
  virtual engine* new_instance() const = 0;
  virtual ~engine_info_dynamic() {};
};

template <typename T>
class engine_info_dynamic_instance : public engine_info_dynamic {
  void add_options(options_description& options) const { T::add_options(options); }
  std::string get_id() const { return T::get_id(); }
  engine* new_instance() const { return T::new_instance(); }
  ~engine_info_dynamic_instance() {}
};

class engine_data {
public:
  typedef std::map<std::string, engine_info_dynamic*> data_map;

  template <typename T>
  void add_engine_info() {
    engine_info_dynamic* info = new engine_info_dynamic_instance<T>();
    d_data[info->get_id()] = info;
  }

  ~engine_data() {
    for (data_map::iterator it = d_data.begin(); it != d_data.end(); ++ it) {
      delete it->second;
    }
  }

  engine_data();

  const data_map& data() const {
    return d_data;
  }

  const engine_info_dynamic& get_engine_info(std::string id) {
    if (d_data.find(id) == d_data.end()) {
      throw new exception("unknown engine: " + id);
    }
    return *d_data[id];
  }

private:

  /** Map from engine ids to the individual engine s_engine_data */
  data_map d_data;

};

/** Map from id's to engine information */
static engine_data s_engine_data;

engine* engine::mk_engine(std::string id) {
  return s_engine_data.get_engine_info(id).new_instance();
}

void engine::add_options(boost::program_options::options_description& options) {
  for (engine_data::data_map::const_iterator it = s_engine_data.data().begin(); it != s_engine_data.data().end(); ++ it) {
    const engine_info_dynamic* info = it->second;
    boost::program_options::options_description engine_options(info->get_id() + " options");
    it->second->add_options(engine_options);
    options.add(engine_options);
  }
}

void engine::get_engines(std::vector<std::string>& out) {
  for (engine_data::data_map::const_iterator it = s_engine_data.data().begin(); it != s_engine_data.data().end(); ++ it) {
    out.push_back(it->second->get_id());
  }
}

//
// ADD ALL THE ENGINES HERE
//
engine_data::engine_data() {
  add_engine_info<bmc::bmc_engine_info>();
}

