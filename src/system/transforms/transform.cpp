#include "transform.h"

#include "add_missing_next.h"
#include "expand_arrays.h"
#include "inlining.h"
#include "promote_nonstate_to_state.h"
#include "remove_arrays.h"
#include "remove_enum_types.h"
#include "remove_subtypes.h"

namespace sally {
namespace cmd {
namespace transforms {

transform::transform(const system::transition_system* original)
: d_original(original)
{
}

factory::register_transform inliner::s_register("inline_functions", 0);
factory::register_transform expand_arrays::s_register("expand_arrays", 1);
factory::register_transform remove_arrays::s_register("remove_arrays", 2);
factory::register_transform remove_enum_types::s_register("remove_enum_types", 3);
factory::register_transform remove_subtypes::s_register("remove_subtypes", 4);
factory::register_transform promote_nonstate_to_state::s_register("promote_nonstate_to_state", 5);
factory::register_transform add_missing_next::s_register("add_missing_next", 6);

factory::info factory::s_info;

factory::transforms_info_map* factory::info::get() {
  if (!m) {
    m = new transforms_info_map();
  }
  return m;
}

factory::register_transform::register_transform(const char* id, size_t priority) {
  assert(s_info.get()->find(id) == s_info.get()->end());
  s_info.get()->operator [] (id) = transform_info(id, priority);
}

std::string factory::get_transforms_list() {
  std::stringstream ss;
  transforms_info_map::const_iterator it = s_info.get()->begin();
  for (bool first = true; it != s_info.get()->end(); ++ it) {
    if (!first) { ss << ", "; }
    if (first) { first = false; }
    ss << it->first;
  }
  return ss.str();
}

struct cmp_info {
  bool operator () (const transform_info& a, const transform_info& b) {
    return a.priority < b.priority;
  }
};

std::string factory::get_default_transforms_list() {
  std::stringstream ss;
  std::vector<transform_info> info;
  transforms_info_map::const_iterator it = s_info.get()->begin();
  for (; it != s_info.get()->end(); ++ it) {
    info.push_back(it->second);
  }
  std::sort(info.begin(), info.end(), cmp_info());

  for (size_t i = 0; i < info.size(); ++ i) {
    if (i) { ss << ","; }
    ss << info[i].id;
  }
  return ss.str();
}

transform* factory::mk_transform(std::string id) {
  return 0;
}

}
}
}
