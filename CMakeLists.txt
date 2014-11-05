cmake_minimum_required(VERSION 2.6)
set(CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")

project(sal2 CXX)
enable_testing()

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Werror -Wall")

# Default is release with debug info
IF(NOT CMAKE_BUILD_TYPE)
SET(CMAKE_BUILD_TYPE RelWithDebInfo CACHE STRING "Choose the type of build, options are: None Debug Release RelWithDebInfo MinSizeRel." FORCE)
ENDIF()

# Add the target for the check
add_custom_target(check COMMAND ${CMAKE_CTEST_COMMAND})

# Find the Boost libraries
find_package(Boost 1.36.0 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIRS})

# Find the GMP number library
find_library(GMP_LIBRARY gmp)
if (GMP_LIBRARY)
  message(STATUS "GMP library: " ${GMP_LIBRARY})
else()
  MESSAGE(FATAL_ERROR "Could not the GMP number library (sudo apt-get libgmp-dev)")
endif()

# Find Yices
SET(YICES_HOME CACHE STRING "Yices2 installation directory")
find_package(Yices2)

# Make sure antlr C runtime is here
include(ExternalProject) 
ExternalProject_Add(
   libantlr3c-3.4
   URL http://www.antlr3.org/download/C/libantlr3c-3.4.tar.gz
   CONFIGURE_COMMAND <SOURCE_DIR>/configure --disable-shared --disable-antlrdebug --prefix=<INSTALL_DIR>
   BUILD_IN_SOURCE 1
)
ExternalProject_Get_Property(libantlr3c-3.4 INSTALL_DIR)
set(LIBANTLR_INCLUDE_DIR "${INSTALL_DIR}/include")
set(LIBANTLR_LIB_DIR "${INSTALL_DIR}/lib")

# Add includes 
include_directories(${sal2_SOURCE_DIR}/src ${YICES_INCLUDE_DIR} ${LIBANTLR_INCLUDE_DIR})

# Configure the subdirectories
add_subdirectory(src)

# Add the test project
add_subdirectory(test)