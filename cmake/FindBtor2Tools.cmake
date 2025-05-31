# - Try to find Btor2Tools
# Once done this will define
#  BTOR2TOOLS_FOUND - System has Btor2Tools
#  BTOR2TOOLS_INCLUDE_DIRS - The Btor2Tools include directories
#  BTOR2TOOLS_LIBRARIES - The libraries needed to use Btor2Tools

if (BTOR2TOOLS_HOME)
  find_path(BTOR2TOOLS_INCLUDE_DIR btor2parser/btor2parser.h PATHS "${BTOR2TOOLS_HOME}/src" NO_DEFAULT_PATH)
else()
  find_path(BTOR2TOOLS_INCLUDE_DIR btor2parser/btor2parser.h)
endif()

if (SALLY_STATIC_BUILD)
  if (BTOR2TOOLS_HOME)
    find_library(BTOR2TOOLS_LIBRARY libbtor2parser.a btor2parser PATHS "${BTOR2TOOLS_HOME}/build/lib" NO_DEFAULT_PATH)
  else()
    find_library(BTOR2TOOLS_LIBRARY libbtor2parser.a btor2parser)
  endif()
else()
  if (BTOR2TOOLS_HOME)
    find_library(BTOR2TOOLS_LIBRARY btor2parser PATHS "${BTOR2TOOLS_HOME}/build/lib" NO_DEFAULT_PATH)
  else()
    find_library(BTOR2TOOLS_LIBRARY btor2parser)
  endif()
endif()

set(BTOR2TOOLS_LIBRARIES ${BTOR2TOOLS_LIBRARY})
set(BTOR2TOOLS_INCLUDE_DIRS ${BTOR2TOOLS_INCLUDE_DIR})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Btor2Tools DEFAULT_MSG BTOR2TOOLS_LIBRARY BTOR2TOOLS_INCLUDE_DIR)

mark_as_advanced(BTOR2TOOLS_INCLUDE_DIR BTOR2TOOLS_LIBRARY) 