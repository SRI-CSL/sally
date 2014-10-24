# - Try to find yices2
# Once done this will define
#  YICES2_FOUND - System has yices2
#  YICES2_INCLUDE_DIRS - The yices2 include directories
#  YICES2_LIBRARIES - The libraries needed to use yices2

find_path(YICES2_INCLUDE_DIR yices.h PATHS ENV YICES_HOME)
find_library(YICES2_LIBRARY libyices PATHS ENV YICES_HOME)

set(YICES2_LIBRARIES ${YICES2_LIBRARY})
set(YICES2_INCLUDE_DIRS ${YICES2_INCLUDE_DIR})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(LibYices2 DEFAULT_MSG YICES2_LIBRARY YICES2_INCLUDE_DIR)

mark_as_advanced(YICES2_INCLUDE_DIR YICES2_LIBRARY)