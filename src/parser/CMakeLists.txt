add_custom_command(
   OUTPUT 
     ${CMAKE_CURRENT_SOURCE_DIR}/mcmtParser.h
     ${CMAKE_CURRENT_SOURCE_DIR}/mcmtParser.c
     ${CMAKE_CURRENT_SOURCE_DIR}/mcmtLexer.h
     ${CMAKE_CURRENT_SOURCE_DIR}/mcmtLexer.c
     ${CMAKE_CURRENT_SOURCE_DIR}/mcmt.tokens
   COMMAND 
     ${ANTLR} -make -fo ${CMAKE_CURRENT_SOURCE_DIR}/ ${CMAKE_CURRENT_SOURCE_DIR}/mcmt.g 
   DEPENDS 
     ${CMAKE_CURRENT_SOURCE_DIR}/mcmt.g
)

set_source_files_properties(
  mcmtParser.c mcmtLexer.c 
  PROPERTIES 
    LANGUAGE CXX
    COMPILE_FLAGS "-Wno-unused-function -Wno-unused-variable"
)

add_library(parser parser.cpp parser_state.cpp mcmtParser.c mcmtLexer.c)
