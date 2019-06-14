# - Try to find OpenSMT2
# Once done this will define
#  OPENSMT2_FOUND - System has OPENSMT2
#  OPENSMT2_INCLUDE_DIRS - The OPENSMT2 include directories
#  OPENSMT2_LIBRARIES - The libraries needed to use OPENSMT2

if (OPENSMT2_HOME)
  find_path(OPENSMT2_INCLUDE_DIR opensmt/opensmt2.h PATHS "${OPENSMT2_HOME}/include")
else() 
  find_path(OPENSMT2_INCLUDE_DIR opensmt/opensmt2.h)
endif()

if (OPENSMT2_HOME)
  find_library(OPENSMT2_LIBRARY opensmt2 PATHS "${OPENSMT2_HOME}/lib")
else() 
  find_library(OPENSMT2_LIBRARY opensmt2)
endif()

# If library found, check the version supports interpolation
if (OPENSMT2_INCLUDE_DIR AND OPENSMT2_LIBRARY)

  # Try to compile with interpolation 
  file(WRITE "${CMAKE_BINARY_DIR}${CMAKE_FILES_DIRECTORY}/CMakeTmp/src.cpp" "
    #include <opensmt/opensmt2.h>
    int main() {
      Opensmt* osmt = new Opensmt(qf_lra, \"osmt_solver\");    
      osmt->getConfig().setLRAInterpolationAlgorithm(itp_alg_pss);
      return 0;
    }
  ")

  # We need to compile as:
  # g++ -std=c++11 -I${OPENSMT2_INCLUDE_DIR} version_test.cpp ${OPENSMT2_LIBRARY} -lgmp

  # Run the test program 
  try_run(
    VERSION_TEST_EXITCODE 
    VERSION_TEST_COMPILED
      ${CMAKE_BINARY_DIR} 
      ${CMAKE_BINARY_DIR}${CMAKE_FILES_DIRECTORY}/CMakeTmp/src.cpp
    COMPILE_DEFINITIONS
      -I"${OPENSMT2_INCLUDE_DIR}"
      -std=c++11
    LINK_LIBRARIES ${OPENSMT2_LIBRARY} gmp
  )  

  if (NOT VERSION_TEST_COMPILED)
    unset(OPENSMT2_INCLUDE_DIR CACHE)
    unset(OPENSMT2_LIBRARY CACHE)
  elseif (NOT ("${VERSION_TEST_EXITCODE}" EQUAL 0))
    unset(OPENSMT2_INCLUDE_DIR CACHE)
    unset(OPENSMT2_LIBRARY CACHE)
  endif()
endif()

set(OPENSMT2_LIBRARIES ${OPENSMT2_LIBRARY})
set(OPENSMT2_INCLUDE_DIRS ${OPENSMT2_INCLUDE_DIR})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(OPENSMT2 DEFAULT_MSG OPENSMT2_LIBRARY OPENSMT2_INCLUDE_DIR)

mark_as_advanced(OPENSMT2_INCLUDE_DIR OPENSMT2_LIBRARY)