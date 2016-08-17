add_ocaml_target("frontend.d.byte")
add_ocaml_target("mcmt_learn.d.byte")

# Add tests

file(GLOB_RECURSE regressions 
  ${sally_SOURCE_DIR}/test/frontend/*.sal 
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
  add_test(${FILE} frontend.d.byte ${ALL_OPTIONS} ${FILE})
  
  # If there is a .gold file, compare the output
  if(EXISTS "${FILE}.gold")
    # Get the gold output
    file(READ "${FILE}.gold" GOLD_OUTPUT)
    # Set the output
    set_tests_properties(${FILE} PROPERTIES PASS_REGULAR_EXPRESSION ${GOLD_OUTPUT})
  endif()
  
endforeach(FILE)
