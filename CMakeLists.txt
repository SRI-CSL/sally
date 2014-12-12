cmake_minimum_required(VERSION 2.6)
set(CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")

project(sal2 CXX)
enable_testing()

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Werror -Wall")

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
find_package(Boost 1.36.0 COMPONENTS program_options iostreams REQUIRED)
include_directories(${Boost_INCLUDE_DIRS})

# Come settings based on word size
if (CMAKE_SIZEOF_VOID_P EQUAL 8)
  set(ANTLR_CONFIG_FLAG "--enable-64bit")
else (CMAKE_SIZEOF_VOID_P EQUAL 8) 
  set(ANTLR_CONFIG_FLAG "")
endif (CMAKE_SIZEOF_VOID_P EQUAL 8)


# Find the GMP number library
find_library(GMP_LIBRARY gmp)
if (GMP_LIBRARY)
  message(STATUS "GMP library: " ${GMP_LIBRARY})
else()
  message(FATAL_ERROR "Could not the GMP number library (sudo apt-get install libgmp-dev)")
endif()

# Find Yices
SET(YICES_HOME CACHE STRING "Yices2 installation directory")
find_package(Yices2)

# Make sure antlr C runtime is here
include(ExternalProject) 
ExternalProject_Add(
   libantlr3c-3.4
   URL "${sal2_SOURCE_DIR}/antlr/libantlr3c-3.4.tar.gz"
   URL_MD5 08b1420129d5dccd0f4461cedf2a0d7d
   CONFIGURE_COMMAND <SOURCE_DIR>/configure ${ANTLR_CONFIG_FLAG} --enable-debuginfo --disable-antlrdebug --prefix=<INSTALL_DIR>
   BUILD_IN_SOURCE 1
)
ExternalProject_Get_Property(libantlr3c-3.4 INSTALL_DIR)
set(ANTLR3C_INCLUDE_DIR "${INSTALL_DIR}/include")
set(ANTLR3C_LIBRARY_DIR "${INSTALL_DIR}/lib")
set(ANTLR3C_LIBRARY "antlr3c")
link_directories(${ANTLR3C_LIBRARY_DIR})

# The antl2 binary
set(ANTLR "${sal2_SOURCE_DIR}/antlr/antlr3")

# Add includes 
include_directories(${sal2_SOURCE_DIR}/src ${YICES_INCLUDE_DIR} ${ANTLR3C_INCLUDE_DIR})

# Configure the subdirectories
add_subdirectory(src)

# Add the test project
add_subdirectory(test)