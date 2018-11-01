# From https://github.com/dreal/dreal-cmake-example-project/blob/master/cmake/modules/FindDreal.cmake

# cmake assumes that dreal can be found by pkg-config. If pkg-config
# cannot find dreal then you will need to add the path directory where
# dreal was installed in the environment variable PKG_CONFIG_PATH.

# This sets the following variables:
# DREAL_FOUND - True if dReal was found.
# DREAL_VERSION - dReal Version
# DREAL_INCLUDE_DIRS - Directories containing the dReal include files.
# DREAL_LIBRARY_DIRS - Directories containing the dReal library files.
# DREAL_LIBRARIES - dReal library names.
# DREAL_DEFINITIONS - Compiler flags for dReal.

if(APPLE)
  set(ENV{PKG_CONFIG_PATH} "/usr/local/opt/ibex@2.7.2/share/pkgconfig:$ENV{PKG_CONFIG_PATH}")
  # TODO(soonho): remove this line when the transition is completed.
  set(ENV{PKG_CONFIG_PATH} "/usr/local/opt/ibex@2.6.5/share/pkgconfig:$ENV{PKG_CONFIG_PATH}")
endif(APPLE)

if(UNIX AND NOT APPLE)
  file(GLOB DREAL_PKG_CONFIG_PATH "/opt/dreal/*/lib/pkgconfig")
  # The result of file-glob is sorted lexicographically. We pick the
  # last element (-1) to pick the latest.
  list(GET DREAL_PKG_CONFIG_PATH -1 DREAL_PKG_CONFIG_PATH)
  set(ENV{PKG_CONFIG_PATH} "${DREAL_PKG_CONFIG_PATH}:/opt/libibex/2.7.2/share/pkgconfig:$ENV{PKG_CONFIG_PATH}")
endif(UNIX AND NOT APPLE)

find_package(PkgConfig)
pkg_check_modules(DREAL dreal)

set(DREAL_DEFINITIONS ${DREAL_CFLAGS_OTHER})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(DREAL
  FOUND_VAR DREAL_FOUND
  REQUIRED_VARS DREAL_INCLUDE_DIRS DREAL_LIBRARIES DREAL_DEFINITIONS
  VERSION_VAR DREAL_VERSION)

mark_as_advanced(DREAL_LIBRARIES DREAL_INCLUDE_DIRS)
