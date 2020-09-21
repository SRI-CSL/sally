# - Try to find LibPoly
# Once done this will define
#  LIBPOLY_FOUND - System has LibPoly
#  LIBPOLY_INCLUDE_DIRS - The LibPoly include directories
#  LIBPOLY_LIBRARIES - The libraries needed to use LibPoly

if (LIBPOLY_HOME)
  find_path(LIBPOLY_INCLUDE_DIR poly/poly.h PATHS "${LIBPOLY_HOME}/include")
else()
  find_path(LIBPOLY_INCLUDE_DIR poly/poly.h)
endif()

if (SALLY_STATIC_BUILD)
  if (LIBPOLY_HOME)
    find_library(LIBPOLY_LIBRARY libpoly.a poly PATHS "${LIBPOLY_HOME}/lib" NO_DEFAULT_PATH)
  else()
    find_library(LIBPOLY_LIBRARY libpoly.a poly)
  endif()
else()
  if (LIBPOLY_HOME)
    find_library(LIBPOLY_LIBRARY poly PATHS "${LIBPOLY_HOME}/lib" NO_DEFAULT_PATH)
  else()
    find_library(LIBPOLY_LIBRARY poly)
  endif()
endif()

# If library found, check the version
if (LIBPOLY_INCLUDE_DIR AND LibPoly_FIND_VERSION)

  # Check version. It is in poly/version.h of the form
  #
  # #define LIBPOLY_VERSION 0.1.1

  # Extract version lines from yices.h
  file(STRINGS "${LIBPOLY_INCLUDE_DIR}/poly/version.h" LIBPOLY_H_VERSION REGEX "#define LIBPOLY_VERSION")
  if("${LIBPOLY_H_VERSION}" MATCHES ".*#define LIBPOLY_VERSION[ ]+([0-9]+\\.[0-9]+\\.[0-9]+).*")
    set(LIBPOLY_VERSION "${CMAKE_MATCH_1}")
  endif()

  # Compare the found version to asked for version
  if ("${LIBPOLY_VERSION}" VERSION_LESS "${LibPoly_FIND_VERSION}")
    unset(LIBPOLY_INCLUDE_DIR CACHE)
    unset(LIBPOLY_LIBRARY CACHE)
  elseif (LibPoly_FIND_VERSION_EXACT AND NOT "${LIBPOLY_VERSION}" VERSION_EQUAL "${LibPoly_FIND_VERSION}")
    unset(LIBPOLY_INCLUDE_DIR CACHE)
    unset(LIBPOLY_LIBRARY CACHE)
  endif()
endif()

set(LIBPOLY_LIBRARIES ${LIBPOLY_LIBRARY})
set(LIBPOLY_INCLUDE_DIRS ${LIBPOLY_INCLUDE_DIR})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(LibPoly DEFAULT_MSG LIBPOLY_LIBRARY LIBPOLY_INCLUDE_DIR)

mark_as_advanced(LIBPOLY_INCLUDE_DIR LIBPOLY_LIBRARY)