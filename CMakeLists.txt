cmake_minimum_required(VERSION 2.6)
set(CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")

project(sally CXX C)
enable_testing()

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Werror -Wall -std=c++11")

# If ENABLE_COVERAGE is defined, try to set coverage flags.
if (ENABLE_COVERAGE)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fprofile-arcs -ftest-coverage")
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_CXX_FLAGS} -fprofile-arcs -ftest-coverage")
  set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_CXX_FLAGS} -fprofile-arcs -ftest-coverage")
endif()

# Default is release with debug info
if(NOT CMAKE_BUILD_TYPE)
set(CMAKE_BUILD_TYPE RelWithDebInfo CACHE STRING "Choose the type of build, options are: None Debug Release RelWithDebInfo MinSizeRel." FORCE)
endif()

# Add the target for the check
add_custom_target(check COMMAND ${CMAKE_CTEST_COMMAND})

# Find the Boost libraries
find_package(Boost 1.53.0 COMPONENTS program_options iostreams thread system REQUIRED)
include_directories(${Boost_INCLUDE_DIRS})

# Come settings based on word size
if (CMAKE_SIZEOF_VOID_P EQUAL 8)
  set(ANTLR_CONFIG_FLAG "--enable-64bit")
else (CMAKE_SIZEOF_VOID_P EQUAL 8) 
  set(ANTLR_CONFIG_FLAG "")
endif (CMAKE_SIZEOF_VOID_P EQUAL 8)


# Find the GMP number library
if (SALLY_STATIC_BUILD)
  find_library(GMP_LIBRARY libgmp.a gmp)
else()
  find_library(GMP_LIBRARY gmp)
endif()
if (GMP_LIBRARY)
  message(STATUS "GMP library: " ${GMP_LIBRARY})
else()
  message(FATAL_ERROR "Could not the GMP number library (sudo apt-get install libgmp-dev)")
endif()

# Find LibPoly
SET(LIBPOLY_HOME CACHE STRING "LibPoly installation directory")
find_package(LibPoly 0.1.5)
if (LIBPOLY_FOUND)
  add_definitions(-DWITH_LIBPOLY)
  include_directories(${LIBPOLY_INCLUDE_DIR})
endif()

# Find Yices if LibPoly is there
if (LIBPOLY_FOUND)
  SET(YICES2_HOME CACHE STRING "Yices2 installation directory")
  find_package(Yices2 2.6.0)
  if (YICES2_FOUND)
    add_definitions(-DWITH_YICES2)
    include_directories(${YICES2_INCLUDE_DIR}) 
  endif()
endif()

# Find MathSAT5
SET(MATHSAT5_HOME CACHE STRING "MathSAT5 installation directory")
find_package(MathSAT5 5.3.3)
if (MATHSAT5_FOUND)
  add_definitions(-DWITH_MATHSAT5)
  include_directories(${MATHSAT5_INCLUDE_DIR})
endif()

# Find Z3
#SET(Z3_HOME CACHE STRING "Z3 installation directory")
#find_package(Z3 4.4.1)
#if (Z3_FOUND)
#  add_definitions(-DWITH_Z3)
#  include_directories(${Z3_INCLUDE_DIR})
#endif()

# Make sure antlr C runtime is here
include(ExternalProject) 
ExternalProject_Add(
   libantlr3c-3.4
   URL "${sally_SOURCE_DIR}/antlr/libantlr3c-3.4.tar.gz"
   URL_MD5 08b1420129d5dccd0f4461cedf2a0d7d
   PATCH_COMMAND chmod -R u+w src include 
         COMMAND patch -p1 -t -N < "${sally_SOURCE_DIR}/antlr/libantlr3c-3.4.patch"
   CONFIGURE_COMMAND <SOURCE_DIR>/configure ${ANTLR_CONFIG_FLAG} --enable-debuginfo --disable-antlrdebug --prefix=<INSTALL_DIR>
   BUILD_IN_SOURCE 1
)
ExternalProject_Get_Property(libantlr3c-3.4 INSTALL_DIR)
set(ANTLR3C_INCLUDE_DIR "${INSTALL_DIR}/include")
set(ANTLR3C_LIBRARY_DIR "${INSTALL_DIR}/lib")
set(ANTLR3C_LIBRARY "antlr3c")
add_library(libantlr3c STATIC IMPORTED)
set_property(TARGET libantlr3c PROPERTY IMPORTED_LOCATION ${ANTLR3C_LIBRARY_DIR}/libantlr3c.a)

# The antl3 binary
set(ANTLR "${sally_SOURCE_DIR}/antlr/antlr3")

# Add includes 
include_directories(${sally_SOURCE_DIR}/src ${ANTLR3C_INCLUDE_DIR})

# Configure the subdirectories
add_subdirectory(src)

# Add the test project
add_subdirectory(test)
