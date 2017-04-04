add_library(ai 
  ai.cpp
  factory.cpp  
  crab/crab.cpp
)
 
target_link_libraries (ai ${CRABMCMT_LIBRARIES}) 
