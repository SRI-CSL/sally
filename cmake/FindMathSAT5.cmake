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
  find_library(MATHSAT5_LIBRARY mathsat PATHS "${MATHSAT5_HOME}/lib")
else() 
  find_library(MATHSAT5_LIBRARY mathsat)
endif()

set(MATHSAT5_LIBRARIES ${MATHSAT5_LIBRARY})
set(MATHSAT5_INCLUDE_DIRS ${MATHSAT5_INCLUDE_DIR})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(MathSAT5 DEFAULT_MSG MATHSAT5_LIBRARY MATHSAT5_INCLUDE_DIR)

mark_as_advanced(MATHSAT5_INCLUDE_DIR MATHSAT5_LIBRARY)