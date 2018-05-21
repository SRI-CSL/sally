set(sally_SRC_DIRS utils expr smt system command parser ai engine)

# Add all the subdirectories
foreach(DIR ${sally_SRC_DIRS})
  add_subdirectory(${DIR})
endforeach(DIR)

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
target_link_libraries(sally ${Boost_LIBRARIES} ${GMP_LIBRARY})

# Add tests

file(GLOB_RECURSE regressions 
  ${sally_SOURCE_DIR}/test/regress/*.mcmt 
  ${sally_SOURCE_DIR}/test/regress/*.btor
  ${sally_SOURCE_DIR}/test/regress/*.sal
)
list(SORT regressions)

foreach(FILE ${regressions})
  # Get the options for this test
  file(READ "${FILE}.options" ALL_OPTIONS)
  # Remove newlines
  string(REGEX REPLACE "(\r?\n)+$" "" ALL_OPTIONS "${ALL_OPTIONS}")
  # Turn the options into a list 
  separate_arguments(ALL_OPTIONS)
  # Add the test with the options and the file
  add_test(${FILE} sally ${ALL_OPTIONS} ${FILE})
  
  # If there is a .gold file, compare the output
  if(EXISTS "${FILE}.gold")
    # Get the gold output
    file(READ "${FILE}.gold" GOLD_OUTPUT)
    # Set the output
    set_tests_properties(${FILE} PROPERTIES PASS_REGULAR_EXPRESSION "${GOLD_OUTPUT}")
  endif()
  
endforeach(FILE)

# Add the install target
install(TARGETS sally DESTINATION bin)
target_link_libraries(sally libantlr3c)
SET(CMAKE_INSTALL_RPATH_USE_LINK_PATH TRUE)
