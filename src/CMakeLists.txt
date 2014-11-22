set(sal2_SRC_DIRS utils expr smt parser system)

# Add all the subdirectories
foreach(DIR ${sal2_SRC_DIRS})
  add_subdirectory(${DIR})
endforeach(DIR)

# Add the execetuble
add_executable(sal2 sal2.cpp)

# Check depdends on the binary
add_dependencies(check sal2)

# Link in all the directories
foreach(DIR ${sal2_SRC_DIRS})
  link_directories(${sal2_BINARY_DIR}/src/${DIR})
  set(sal2_LIBS ${DIR} ${sal2_LIBS})
endforeach(DIR)

# Link in all the other libraries
target_link_libraries(sal2 ${sal2_LIBS} ${Boost_LIBRARIES} ${GMP_LIBRARY} ${YICES_LIBRARY} ${ANTLR3C_LIBRARY})

# Add tests

file(GLOB_RECURSE regressions ${sal2_SOURCE_DIR}/test/regress/*.mcmt)
list(SORT regressions)

foreach(FILE ${regressions})
  file(STRINGS "${FILE}.options" ALL_OPTIONS)
  foreach(OPTIONS ${ALL_OPTIONS})
    add_test(${FILE} sal2 ${OPTIONS} ${FILE})
  endforeach(OPTIONS)
endforeach(FILE)