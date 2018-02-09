add_library(system 
  state_type.cpp
  state_formula.cpp
  transition_formula.cpp
  transition_system.cpp
  trace_helper.cpp
  context.cpp
  transforms/transform.cpp
  transforms/expand_arrays.cpp
  transforms/remove_arrays.cpp
  transforms/remove_enum_types.cpp
  transforms/remove_subtypes.cpp
  transforms/promote_nonstate_to_state.cpp
  transforms/add_missing_next.cpp
  transforms/inlining.cpp
  transforms/preprocessor.cpp
)
 