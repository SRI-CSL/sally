set(sally_SRC_DIRS utils expr smt system command parser engine)

# Add all the subdirectories
foreach(DIR ${sally_SRC_DIRS})
  add_subdirectory(${DIR})
endforeach(DIR)

if (DREAL_FOUND)
  # It must be added before add_executable
  link_directories(${DREAL_LIBRARY_DIRS})
endif()

# Add the executable
add_executable(sally sally.cpp)
if (SALLY_STATIC_BUILD)
  set_target_properties(sally PROPERTIES LINK_FLAGS "-static")
  set_target_properties (sally PROPERTIES LINK_SEARCH_START_STATIC ON)
  set_target_properties (sally PROPERTIES LINK_SEARCH_END_STATIC ON)
endif()

# Check depends on the binary
add_dependencies(check sally)

# Link in all the directories
foreach(DIR ${sally_SRC_DIRS})
  link_directories(${sally_BINARY_DIR}/src/${DIR})
  set(sally_LIBS ${DIR} ${sally_LIBS})
endforeach(DIR)

# Link in all the other libraries
target_link_libraries(sally ${sally_LIBS})
if (YICES2_FOUND)
  target_link_libraries(sally ${YICES2_LIBRARY})
endif()
if (LIBPOLY_FOUND)
  target_link_libraries(sally ${LIBPOLY_LIBRARY})
endif()
if (MATHSAT5_FOUND)
  target_link_libraries(sally ${MATHSAT5_LIBRARY})
endif()
if (Z3_FOUND)
  target_link_libraries(sally ${Z3_LIBRARY})
endif()
if (OPENSMT2_FOUND)
  target_link_libraries(sally ${OPENSMT2_LIBRARY})
endif()
if (DREAL_FOUND)
  target_link_libraries(sally ${DREAL_LIBRARIES})
endif()
if (BTOR2TOOLS_FOUND)
  target_link_libraries(sally -lbtor2parser)
endif()

target_link_libraries(sally ${Boost_LIBRARIES} ${GMP_LIBRARY})

# Add tests

# Build the list of regression files based on available solvers
set(regression_patterns
  ${sally_SOURCE_DIR}/test/regress/**/*.mcmt 
  ${sally_SOURCE_DIR}/test/regress/**/*.btor
  ${sally_SOURCE_DIR}/test/regress/**/*.sal
)

# Add btor2 files only if Btor2Tools is found
if (BTOR2TOOLS_FOUND)
  list(APPEND regression_patterns ${sally_SOURCE_DIR}/test/regress/**/*.btor2)
endif()

# Get all the regression files
file(GLOB_RECURSE regressions ${regression_patterns})
list(SORT regressions)


foreach(FILE ${regressions})
  # Get the options for this test
  file(READ "${FILE}.options" ALL_OPTIONS)
  # Remove newlines
  string(REGEX REPLACE "(\r?\n)+$" "" ALL_OPTIONS "${ALL_OPTIONS}")
  # Turn the options into a list 
  separate_arguments(ALL_OPTIONS)

  # Don't run tests that require a solver not supported 
  list (FIND ALL_OPTIONS "dreal" FIND_INDEX)
  if ((NOT DREAL_FOUND) AND (FIND_INDEX GREATER -1))
    continue()
  endif()

  # Don't run tests that require a solver not supported 
  list (FIND ALL_OPTIONS "d4y2" FIND_INDEX)
  if (((NOT DREAL_FOUND) OR (NOT YICES2_FOUND)) AND (FIND_INDEX GREATER -1))
    continue()
  endif()

  # Don't run tests that require a solver not supported 
  list (FIND ALL_OPTIONS "y2o2" FIND_INDEX)
  if (((NOT OPENSMT2_FOUND) OR (NOT YICES2_FOUND)) AND (FIND_INDEX GREATER -1))
    continue()
  endif()

  # Add the test with the options and the file
  add_test(${FILE} sally ${ALL_OPTIONS} ${FILE})
  
  # If there is a .gold file, compare the output
  if(EXISTS "${FILE}.gold")
    # Get the gold output
    file(READ "${FILE}.gold" GOLD_OUTPUT)
    # Set the output
    set_tests_properties(${FILE} PROPERTIES 
      PASS_REGULAR_EXPRESSION "${GOLD_OUTPUT}"
      TIMEOUT 60
    )
  endif()
  
endforeach(FILE)

# Add the install target
install(TARGETS sally DESTINATION bin)
target_link_libraries(sally libantlr3c)
SET(CMAKE_INSTALL_RPATH_USE_LINK_PATH TRUE)
