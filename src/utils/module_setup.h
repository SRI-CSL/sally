/*
 * module_setup.h
 *
 *  Created on: Nov 26, 2014
 *      Author: dejan
 */

#pragma once

#include <map>
#include <boost/program_options/options_description.hpp>

//
// Utilities for factories of modules. Only include this in the factory
// implementations.
//

namespace sal2 {

/**
 * Class to get information about a module, setup options requrired by the
 * module and create new module instances.
 */
template <typename module_type, typename constructor_type>
struct module_info_dynamic {
  virtual void setup_options(boost::program_options::options_description& options) const = 0;
  virtual std::string get_id() const = 0;
  virtual module_type* new_instance(const constructor_type& ctx) const = 0;
  virtual ~module_info_dynamic() {};
};

/**
 * Given T that implements the interfact of module_info_dynamic with
 * static methods, the class implements them as regular methods.
 */
template <typename T, typename module_type, typename constructor_type>
class module_info_dynamic_instance : public module_info_dynamic<module_type, constructor_type> {
  void setup_options(boost::program_options::options_description& options) const { T::setup_options(options); }
  std::string get_id() const { return T::get_id(); }
  module_type* new_instance(const constructor_type& ctx) const { return T::new_instance(ctx); }
  ~module_info_dynamic_instance() {}
};

/**
 * Class encapsulating the data about several modules of the same type.
 */
template <typename module_type, typename constructor_type>
class module_data {
public:

  typedef module_info_dynamic<module_type, constructor_type> module_info;
  typedef std::map<std::string, module_info*> data_map;

  typedef typename data_map::const_iterator const_iterator;
  typedef typename data_map::iterator iterator;

  template <typename T>
  void add_module_info() {
    module_info* info = new module_info_dynamic_instance<T, module_type, constructor_type>();
    d_data[info->get_id()] = info;
  }

  module_data() {}

  ~module_data() {
    for (iterator it = d_data.begin(); it != d_data.end(); ++ it) {
      delete it->second;
    }
  }

  /** Get the data */
  const data_map& data() const {
    return d_data;
  }

  /** Get the info for a particular module */
  const module_info& get_module_info(std::string id) {
    if (d_data.find(id) == d_data.end()) {
      throw exception("unknown module: " + id);
    }
    return *d_data[id];
  }

private:

  /** Map from engine ids to the individual engine s_engine_data */
  data_map d_data;
};

}
