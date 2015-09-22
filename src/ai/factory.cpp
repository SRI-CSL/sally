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

#include "ai/factory.h"
#include "utils/exception.h"
#include "utils/module_setup.h"

#include <vector>
#include <map>

namespace sally {

/** Type for setting up individual engines */
class analyzer_data : public module_data<analyzer, system::context> {
public:
  analyzer_data();
};

/** Map from id's to engine information */
static analyzer_data s_analyzer_data;

analyzer* factory::mk_analyzer(std::string id, const system::context& ctx) {
  return s_analyzer_data.get_module_info(id).new_instance(ctx);
}

void factory::setup_options(boost::program_options::options_description& options) {
  for (analyzer_data::const_iterator it = s_analyzer_data.data().begin(); it != s_analyzer_data.data().end(); ++ it) {
    std::stringstream ss;
    ss << "Analyzer '" << it->second->get_id() << "' options";
    boost::program_options::options_description analyzer_options(ss.str());
    it->second->setup_options(analyzer_options);
    if (analyzer_options.options().size() > 0) {
      options.add(analyzer_options);
    }
  }
}

void factory::get_analyzers(std::vector<std::string>& out) {
  for (analyzer_data::const_iterator it = s_analyzer_data.data().begin(); it != s_analyzer_data.data().end(); ++ it) {
    out.push_back(it->second->get_id());
  }
}

}

#include "analyzer_list.h"
