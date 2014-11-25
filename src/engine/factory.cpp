/*
 * factory.cpp
 *
 *  Created on: Nov 25, 2014
 *      Author: dejan
 */

#include "engine/factory.h"
#include "utils/exception.h"

#include <vector>
#include <map>

using namespace boost::program_options;

namespace sal2 {

struct engine_info_dynamic {
  virtual void setup_options(options_description& options) const = 0;
  virtual std::string get_id() const = 0;
  virtual engine* new_instance(const system::context& ctx) const = 0;
  virtual ~engine_info_dynamic() {};
};

template <typename T>
class engine_info_dynamic_instance : public engine_info_dynamic {
  void setup_options(options_description& options) const { T::setup_options(options); }
  std::string get_id() const { return T::get_id(); }
  engine* new_instance(const system::context& ctx) const { return T::new_instance(ctx); }
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
      throw exception("unknown engine: " + id);
    }
    return *d_data[id];
  }

private:

  /** Map from engine ids to the individual engine s_engine_data */
  data_map d_data;

};

/** Map from id's to engine information */
static engine_data s_engine_data;

engine* factory::mk_engine(std::string id, const system::context& ctx) {
  return s_engine_data.get_engine_info(id).new_instance(ctx);
}

void factory::setup_options(boost::program_options::options_description& options) {
  for (engine_data::data_map::const_iterator it = s_engine_data.data().begin(); it != s_engine_data.data().end(); ++ it) {
    const engine_info_dynamic* info = it->second;
    boost::program_options::options_description engine_options(info->get_id() + " options");
    it->second->setup_options(engine_options);
    options.add(engine_options);
  }
}

void factory::get_engines(std::vector<std::string>& out) {
  for (engine_data::data_map::const_iterator it = s_engine_data.data().begin(); it != s_engine_data.data().end(); ++ it) {
    out.push_back(it->second->get_id());
  }
}

}

#include "engine/engines_list.h"
