add_library(engine 
  engine.cpp
  factory.cpp 
  bmc/bmc_engine.cpp
  kind/kind_engine.cpp
  pdkind/reachability.cpp  
  pdkind/pdkind_engine.cpp  
  pdkind/solvers.cpp
  pdkind/induction_obligation.cpp
  pdkind/cex_manager.cpp
  translator/translator.cpp
)

