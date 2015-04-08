add_library(smt 
  solver.cpp
  incremental_wrapper.cpp
  delayed_wrapper.cpp
  smt2_output_wrapper.cpp
  factory.cpp 
  yices2/yices2.cpp
  yices2/yices2_internal.cpp
  yices2/yices2_term_cache.cpp 
  mathsat5/mathsat5.cpp
  mathsat5/mathsat5_term_cache.cpp
  y2m5/y2m5.cpp
  generic/generic_solver.cpp
)

