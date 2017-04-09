add_library(ai 
  ai.cpp
  factory.cpp  
  crab/crab.cpp
  )

## Needed by 
if (SALLY_STATIC_BUILD)
  find_library(GMPXX_LIBRARY libgmpxx.a gmpxx)
else()  
  find_library(GMPXX_LIBRARY gmpxx)
endif()

target_link_libraries (ai ${CRABMCMT_LIBRARIES} ${GMPXX_LIBRARY})

