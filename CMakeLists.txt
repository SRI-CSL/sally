cmake_minimum_required(VERSION 2.6)

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

# Add our sources to the include
include_directories(${sal2_SOURCE_DIR}/src)

# Configure the subdirectories
add_subdirectory(src)

# Add the test project
add_subdirectory(test)