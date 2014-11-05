set(sal2_SRC_DIRS utils expr smt parser)

foreach(DIR ${sal2_SRC_DIRS})
  add_subdirectory(${DIR})
endforeach(DIR)

add_executable(sal2 sal2.cpp)
add_dependencies(check sal2)

foreach(DIR ${sal2_SRC_DIRS})
  link_directories(${sal2_BINARY_DIR}/src/${DIR})
  set(sal2_LIBS ${DIR} ${sal2_LIBS})
endforeach(DIR)

target_link_libraries(sal2 ${sal2_LIBS} ${Boost_LIBRARIES} ${GMP_LIBRARY} ${YICES_LIBRARY} ${ANTLR3C_LIBRARY})
