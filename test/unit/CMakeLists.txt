# Find the Boost unit test library
find_package(Boost 1.36.0 COMPONENTS unit_test_framework iostreams program_options REQUIRED)

if (DREAL_FOUND)
  # It must be added before add_executable
  link_directories(${DREAL_LIBRARY_DIRS})
endif()

# The binary
ADD_DEFINITIONS(-DBOOST_TEST_DYN_LINK) 
add_executable(sally_test test_runner.cpp)
add_dependencies(check sally_test)

# Original sally libraries
foreach (DIR utils expr smt)
  link_directories(${sally_BINARY_DIR}/src/${DIR})
  set(sally_test_LIBS ${DIR} ${sally_test_LIBS})
endforeach(DIR)

# The test libraries
foreach (DIR expr smt)
  add_subdirectory(${DIR})
  # We need to add the options, to include the whole library, otherwise boost
  # auto-registration of tests doesn't work.
  if(APPLE) 
    set(sally_test_LIBS -Wl,-force_load ${DIR}_test ${sally_test_LIBS})    
  else()
   set(sally_test_LIBS -Wl,--whole-archive ${DIR}_test -Wl,--no-whole-archive ${sally_test_LIBS})
  endif()
endforeach(DIR)

# Link the thing
target_link_libraries(sally_test ${sally_test_LIBS} ${Boost_LIBRARIES})
if (LIBPOLY_FOUND)
  target_link_libraries(sally_test ${LIBPOLY_LIBRARY})
endif()
if (YICES2_FOUND)
  target_link_libraries(sally_test ${YICES2_LIBRARY})
endif()
if (MATHSAT5_FOUND)
  target_link_libraries(sally_test ${MATHSAT5_LIBRARY})
endif()
if (Z3_FOUND)
  target_link_libraries(sally_test ${Z3_LIBRARY})
endif()
if (OPENSMT2_FOUND)
  target_link_libraries(sally_test ${OPENSMT2_LIBRARY})
endif()
if (DREAL_FOUND)
  target_link_libraries(sally_test ${DREAL_LIBRARIES})
endif()

target_link_libraries(sally_test ${GMP_LIBRARY})

# Add the test
add_test(unit_tests sally_test -i)
