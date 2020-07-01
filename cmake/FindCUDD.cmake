# - Try to find LibPoly
# Once done this will define
#  CUDD_FOUND - System has LibPoly
#  CUDD_INCLUDE_DIRS - The LibPoly include directories
#  CUDD_LIBRARIES - The libraries needed to use LibPoly

if (CUDD_HOME)
  find_path(CUDD_INCLUDE_DIR cudd.h PATHS "${CUDD_HOME}/include" NO_DEFAULT_PATH)
else() 
  find_path(CUDD_INCLUDE_DIR cudd.h)
endif()

if (SALLY_STATIC_BUILD)
  if (CUDD_HOME)
    find_library(CUDD_LIBRARY libcudd.a cudd PATHS "${CUDD_HOME}/lib" NO_DEFAULT_PATH)
  else() 
    find_library(CUDD_LIBRARY libcudd.a cudd)
  endif()
else()
  if (CUDD_HOME)
    find_library(CUDD_LIBRARY cudd PATHS "${CUDD_HOME}/lib" NO_DEFAULT_PATH)
  else() 
    find_library(CUDD_LIBRARY cudd)
  endif()
endif()

set(CUDD_LIBRARIES ${CUDD_LIBRARY})
set(CUDD_INCLUDE_DIRS ${CUDD_INCLUDE_DIR})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(CUDD DEFAULT_MSG CUDD_LIBRARY CUDD_INCLUDE_DIR)

mark_as_advanced(CUDD_INCLUDE_DIR CUDD_LIBRARY)