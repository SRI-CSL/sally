# - Try to find crab-mcmt
# Once done this will define
#  CRABMCMT_FOUND - System has crab-mcmt
#  CRABMCMT_INCLUDE_DIRS - The crab-mcmt include directories
#  CRABMCMT_LIBRARIES - The libraries needed to use crab-mcmt

if (CRABMCMT_HOME)
  find_path(CRABMCMT_INCLUDE_DIR crab_mcmt/crab_mcmt.hpp PATHS "${CRABMCMT_HOME}/include" NO_DEFAULT_PATH)
else() 
  find_path(CRABMCMT_INCLUDE_DIR crab_mcmt/crab_mcmt.hpp NO_DEFAULT_PATH)
endif()


if (CRABMCMT_HOME)
  find_library(CRABMCMT_LIBRARY crab_mcmt PATHS "${CRABMCMT_HOME}/lib" NO_DEFAULT_PATH)
  find_library(CRAB_LIBRARY Crab PATHS "${CRABMCMT_HOME}/lib" NO_DEFAULT_PATH)
endif()

set(CRABMCMT_LIBRARIES ${CRABMCMT_LIBRARY} ${CRAB_LIBRARY})
set(CRABMCMT_INCLUDE_DIRS ${CRABMCMT_INCLUDE_DIR})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(CrabMcmt
  DEFAULT_MSG CRABMCMT_LIBRARY CRAB_LIBRARY CRABMCMT_INCLUDE_DIR)

mark_as_advanced(CRABMCMT_INCLUDE_DIR CRABMCMT_LIBRARY CRAB_LIBRARY)
