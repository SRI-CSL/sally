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
  z3/z3.cpp
  z3/z3_internal.cpp
  z3/z3_common.cpp
  y2z3/y2z3.cpp
  opensmt2/opensmt2.cpp
  opensmt2/opensmt2_internal.cpp
  opensmt2/opensmt2_term_cache.cpp
  y2o2/y2o2.cpp
  dreal/dreal.cpp
  dreal/dreal_term.cpp  
  dreal/dreal_internal.cpp
  dreal/dreal_term_cache.cpp
  d4y2/d4y2.cpp
)

if (OPENSMT2_FOUND)
set_source_files_properties(
  opensmt2/opensmt2.cpp opensmt2/opensmt2_internal.cpp opensmt2/opensmt2_term_cache.cpp
  PROPERTIES 
    LANGUAGE CXX
    COMPILE_FLAGS "-std=c++11 -DPRODUCE_PROOF" 
)
endif()

# For dreal
if (DREAL_FOUND)
set_source_files_properties(
  dreal/dreal.cpp dreal/dreal_term.cpp dreal/dreal_internal.cpp dreal/dreal_term_cache.cpp
  PROPERTIES 
    LANGUAGE CXX
    COMPILE_FLAGS "-Wno-unused-variable -Wno-overloaded-virtual -Wno-unknown-pragmas -Wno-int-in-bool-context -Wno-deprecated -Wno-unknown-warning-option -std=c++14"
)
endif()


