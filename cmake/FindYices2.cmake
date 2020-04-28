# - Try to find yices2
# Once done this will define
#  YICES2_FOUND - System has yices2
#  YICES2_INCLUDE_DIRS - The yices2 include directories
#  YICES2_LIBRARIES - The libraries needed to use yices2

if (YICES2_HOME)
  find_path(YICES2_INCLUDE_DIR yices.h PATHS "${YICES2_HOME}/include")
else() 
  find_path(YICES2_INCLUDE_DIR yices.h)
endif()

if (SALLY_STATIC_BUILD)
  if (YICES2_HOME)
    find_library(YICES2_LIBRARY libyices.a yices PATHS "${YICES2_HOME}/lib")
  else() 
    find_library(YICES2_LIBRARY libyices.a yices)
  endif()
else()
  if (YICES2_HOME)
    find_library(YICES2_LIBRARY yices PATHS "${YICES2_HOME}/lib")
  else() 
    find_library(YICES2_LIBRARY yices)
  endif()
endif()

# If library found, check the version
if (YICES2_INCLUDE_DIR AND Yices2_FIND_VERSION)

  # Check version. It is in yices.h of the form 
  # 
  # #define __YICES_VERSION            2
  # #define __YICES_VERSION_MAJOR      3
  # #define __YICES_VERSION_PATCHLEVEL 0

  # Extract version lines from yices.h
  file(STRINGS "${YICES2_INCLUDE_DIR}/yices.h" __YICES_H_VERSIONS REGEX "#define __YICES_VERSION")
  foreach(v __YICES_VERSION __YICES_VERSION_MAJOR __YICES_VERSION_PATCHLEVEL)
    if("${__YICES_H_VERSIONS}" MATCHES ".*#define ${v}[ ]+([0-9]+).*")
      set(${v} "${CMAKE_MATCH_1}")
    endif()
  endforeach()

  set(__YICES_H_VERSION "${__YICES_VERSION}.${__YICES_VERSION_MAJOR}.${__YICES_VERSION_PATCHLEVEL}")

  # Compare the found version to asked for version
  if ("${__YICES_H_VERSION}" VERSION_LESS "${Yices2_FIND_VERSION}")
     unset(YICES2_INCLUDE_DIR CACHE)
     unset(YICES2_LIBRARY CACHE)
  elseif (Yices2_FIND_VERSION_EXACT AND NOT "${__YICES_H_VERSION}" VERSION_EQUAL "${Yices2_FIND_VERSION}")
     unset(YICES2_INCLUDE_DIR CACHE)
     unset(YICES2_LIBRARY CACHE) 
  endif()
  
  # Try to compile and check for MCSAT
  file(WRITE "${CMAKE_BINARY_DIR}${CMAKE_FILES_DIRECTORY}/CMakeTmp/yices2.c" "
    #include <stdio.h>
    #include \"yices.h\"

    int main() {
      int ok = yices_has_mcsat();
      if (!ok) {
        return -1;
      }
      return 0;
    }
  ")
  
  # We need to compile as:
  # gcc -I${YICES2_INCLUDE_DIR} -I${GMP_INCLUDE} version_test.cpp ${YICES2_LIBRARY} ${LIBPOLY_LIBRARY} ${GMP_LIBRARY} 

  # Run the test program 
  try_run(
    MCSAT_TEST_EXITCODE 
    MCSAT_TEST_COMPILED
    ${CMAKE_BINARY_DIR} 
    ${CMAKE_BINARY_DIR}${CMAKE_FILES_DIRECTORY}/CMakeTmp/yices2.c
    COMPILE_DEFINITIONS
      -I"${YICES2_INCLUDE_DIR}"
      -I"${LIBPOLY_INCLUDE_DIR}"
      -I"${GMP_INCLUDE}"
    LINK_LIBRARIES
      ${YICES2_LIBRARY} ${LIBPOLY_LIBRARY} ${GMP_LIBRARY} 
    CMAKE_FLAGS
      -DCMAKE_SKIP_RPATH:BOOL=${CMAKE_SKIP_RPATH}       
    RUN_OUTPUT_VARIABLE
      MCSAT_TEST_RUN_OUTPUT
    COMPILE_OUTPUT_VARIABLE
      MCSAT_TEST_COMPILE_OUTPUT
  )  
  
  if (NOT MCSAT_TEST_COMPILED)
    unset(YICES2_INCLUDE_DIR CACHE)
    unset(YICES2_LIBRARY CACHE)
  elseif (NOT ("${MCSAT_TEST_EXITCODE}" EQUAL 0))
    unset(YICES2_INCLUDE_DIR CACHE)
    unset(YICES2_LIBRARY CACHE)
    message(STATUS "Yices2 found, but doesn't have MCSAT enabled (configure Yices2 with --enable-mcsat).")
  endif()
  
endif()

set(YICES2_LIBRARIES ${YICES2_LIBRARY})
set(YICES2_INCLUDE_DIRS ${YICES2_INCLUDE_DIR})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Yices2 DEFAULT_MSG YICES2_LIBRARY YICES2_INCLUDE_DIR)

mark_as_advanced(YICES2_INCLUDE_DIR YICES2_LIBRARY)