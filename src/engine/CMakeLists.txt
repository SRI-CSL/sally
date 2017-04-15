add_library(engine 
  engine.cpp
  factory.cpp 
  bmc/bmc_engine.cpp
  kind/kind_engine.cpp
  ic3/reachability.cpp  
  ic3/ic3_engine.cpp  
  ic3/solvers.cpp
  ic3/induction_obligation.cpp
  ic3/cex_manager.cpp
  translator/translator.cpp
)

