set(sal2_SRC_DIRS utils expr smt system parser engine)

# Add all the subdirectories
foreach(DIR ${sal2_SRC_DIRS})
  add_subdirectory(${DIR})
endforeach(DIR)

# Add the executable
add_executable(sal2 sal2.cpp)

# Check depends on the binary
add_dependencies(check sal2)

# Link in all the directories
foreach(DIR ${sal2_SRC_DIRS})
  link_directories(${sal2_BINARY_DIR}/src/${DIR})
  set(sal2_LIBS ${DIR} ${sal2_LIBS})
endforeach(DIR)

# Link in all the other libraries
target_link_libraries(sal2 ${sal2_LIBS} ${Boost_LIBRARIES} ${GMP_LIBRARY} ${ANTLR3C_LIBRARY})
if (YICES2_FOUND)
  target_link_libraries(sal2 ${YICES2_LIBRARY})
endif()
if (MATHSAT5_FOUND)
  target_link_libraries(sal2 ${MATHSAT5_LIBRARY})
endif()

# Add tests

file(GLOB_RECURSE regressions 
  ${sal2_SOURCE_DIR}/test/regress/*.mcmt 
  ${sal2_SOURCE_DIR}/test/regress/*.btor
  ${sal2_SOURCE_DIR}/test/regress/*.sal
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
  add_test(${FILE} sal2 ${ALL_OPTIONS} ${FILE})
  
  # If there is a .gold file, compare the output
  if(EXISTS "${FILE}.gold")
    # Get the gold output
    file(READ "${FILE}.gold" GOLD_OUTPUT)
    # Set the output
    set_tests_properties(${FILE} PROPERTIES PASS_REGULAR_EXPRESSION ${GOLD_OUTPUT})
  endif()
  
endforeach(FILE)