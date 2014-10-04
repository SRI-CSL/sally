# Find the Boost unit test library
find_package(Boost 1.36.0 COMPONENTS unit_test_framework REQUIRED)

# The binary
ADD_DEFINITIONS(-DBOOST_TEST_DYN_LINK) 
add_executable(sal2_test test_runner.cpp)
add_dependencies(check sal2_test)

# Original sal2 libraries
foreach (DIR utils expr)
  link_directories(${sal2_BINARY_DIR}/src/${DIR})
  set(sal2_test_LIBS ${DIR} ${sal2_test_LIBS})
endforeach(DIR)

# The test libraries
foreach (DIR expr)
  add_subdirectory(${DIR})
  # We need to add the options, to include the whole library, otherwise boost
  # auto-registration of tests doesn't work.
  set(sal2_test_LIBS -Wl,--whole-archive ${DIR}_test -Wl,--no-whole-archive ${sal2_test_LIBS})
endforeach(DIR)

# Link the thing
target_link_libraries(sal2_test ${sal2_test_LIBS} ${Boost_LIBRARIES} ${GMP_LIBRARY})

# Add the test
add_test(unit_tests sal2_test -i)