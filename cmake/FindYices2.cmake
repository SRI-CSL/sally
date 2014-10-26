# - Try to find yices2
# Once done this will define
#  YICES_FOUND - System has yices2
#  YICES_INCLUDE_DIRS - The yices2 include directories
#  YICES_LIBRARIES - The libraries needed to use yices2

if (YICES_HOME)
  find_path(YICES_INCLUDE_DIR yices.h PATHS "${YICES_HOME}/include")
else() 
  find_path(YICES_INCLUDE_DIR yices.h)
endif()

if (YICES_HOME)
  find_library(YICES_LIBRARY yices PATHS "${YICES_HOME}/lib")
else() 
  find_library(YICES_LIBRARY yices)
endif()

set(YICES_LIBRARIES ${YICES_LIBRARY})
set(YICES_INCLUDE_DIRS ${YICES_INCLUDE_DIR})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Yices2 DEFAULT_MSG YICES_LIBRARY YICES_INCLUDE_DIR)

mark_as_advanced(YICES_INCLUDE_DIR YICES_LIBRARY)