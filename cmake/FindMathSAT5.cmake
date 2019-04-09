# - Try to find MathSAT5
# Once done this will define
#  MATHSAT5_FOUND - System has mathsat5
#  MATHSAT5_INCLUDE_DIRS - The mathsat5 include directories
#  MATHSAT5_LIBRARIES - The libraries needed to use mathsat5

if (MATHSAT5_HOME)
  find_path(MATHSAT5_INCLUDE_DIR mathsat.h PATHS "${MATHSAT5_HOME}/include")
else() 
  find_path(MATHSAT5_INCLUDE_DIR mathsat.h)
endif()

if (MATHSAT5_HOME)
  find_library(MATHSAT5_LIBRARY libmathsat.a mathsat PATHS "${MATHSAT5_HOME}/lib")
else() 
  find_library(MATHSAT5_LIBRARY libmathsat.a mathsat)
endif()

# If library found, check the version
if (MATHSAT5_INCLUDE_DIR AND MATHSAT5_LIBRARY AND MathSAT5_FIND_VERSION)

	# Check version from char *msat_get_version(void)
  file(WRITE "${CMAKE_BINARY_DIR}${CMAKE_FILES_DIRECTORY}/CMakeTmp/src.cpp" "
    #include <stdio.h>
    #include \"mathsat.h\"

    int main() {
      char *version = msat_get_version();
      printf(\"%s\\n\", version);
      msat_free(version);
      return 0;
    }
  ")

  # We need to compile as:
  # gcc -I${MATHSAT5_INCLUDE_DIR} version_test.cpp ${MATHSAT5_LIBRARY} -lgmp

  # Run the test program 
  try_run(
    VERSION_TEST_EXITCODE 
    VERSION_TEST_COMPILED
    ${CMAKE_BINARY_DIR} 
    ${CMAKE_BINARY_DIR}${CMAKE_FILES_DIRECTORY}/CMakeTmp/src.cpp
    COMPILE_DEFINITIONS
      -I"${MATHSAT5_INCLUDE_DIR}"
      LINK_LIBRARIES ${MATHSAT5_LIBRARY} gmp
    CMAKE_FLAGS
      -DCMAKE_SKIP_RPATH:BOOL=${CMAKE_SKIP_RPATH}       
    RUN_OUTPUT_VARIABLE 
      VERSION_TEST_RUN_OUTPUT
  )  

	if (NOT VERSION_TEST_COMPILED)
  	unset(MATHSAT5_INCLUDE_DIR CACHE)
    unset(MATHSAT5_LIBRARY CACHE)
  elseif (NOT ("${VERSION_TEST_EXITCODE}" EQUAL 0))
    unset(MATHSAT5_INCLUDE_DIR CACHE)
    unset(MATHSAT5_LIBRARY CACHE)
  else()
    # Output is of the form:
    # MathSAT5 version 5.3.3 (6e07638491c6) (Feb 27 2015 14:29:04, gmp 5.1.3, gcc 4.6.3, 64-bit)
    if("${VERSION_TEST_RUN_OUTPUT}" MATCHES "MathSAT5 version ([0-9]*\\.[0-9]*\\.[0-9]*).*")
      set(MATHSAT5_VERSION "${CMAKE_MATCH_1}")
  	  if ("${MATHSAT5_VERSION}" VERSION_LESS "${MathSAT5_FIND_VERSION}")
    	  unset(MATHSAT5_INCLUDE_DIR CACHE)
    	  unset(MATHSAT5_LIBRARY CACHE)
  	  elseif (MathSAT5_FIND_VERSION_EXACT AND NOT "${MATHSAT5_VERSION}" VERSION_EQUAL "${MathSAT5_FIND_VERSION}")
    	  unset(MATHSAT5_INCLUDE_DIR CACHE)
     	  unset(MATHSAT5_LIBRARY CACHE)
  	  endif()
    else()
   	  unset(MATHSAT5_INCLUDE_DIR CACHE)
  	  unset(MATHSAT5_LIBRARY CACHE)      
    endif()
  endif()
endif()

set(MATHSAT5_LIBRARIES ${MATHSAT5_LIBRARY})
set(MATHSAT5_INCLUDE_DIRS ${MATHSAT5_INCLUDE_DIR})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(MathSAT5 DEFAULT_MSG MATHSAT5_LIBRARY MATHSAT5_INCLUDE_DIR)

mark_as_advanced(MATHSAT5_INCLUDE_DIR MATHSAT5_LIBRARY)