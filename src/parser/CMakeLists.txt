add_custom_command(
   OUTPUT 
     ${CMAKE_CURRENT_SOURCE_DIR}/mcmt/mcmtParser.h
     ${CMAKE_CURRENT_SOURCE_DIR}/mcmt/mcmtParser.c
     ${CMAKE_CURRENT_SOURCE_DIR}/mcmt/mcmtLexer.h
     ${CMAKE_CURRENT_SOURCE_DIR}/mcmt/mcmtLexer.c
     ${CMAKE_CURRENT_SOURCE_DIR}/mcmt/mcmt.tokens
   COMMAND 
     ${ANTLR} -make -fo ${CMAKE_CURRENT_SOURCE_DIR}/mcmt/ ${CMAKE_CURRENT_SOURCE_DIR}/mcmt/mcmt.g 
   DEPENDS 
     ${CMAKE_CURRENT_SOURCE_DIR}/mcmt/mcmt.g libantlr3c-3.4
)

set_source_files_properties(
  mcmt/mcmtParser.c mcmt/mcmtLexer.c 
  PROPERTIES 
    LANGUAGE CXX
    COMPILE_FLAGS "-Wno-unused-function -Wno-unused-variable -Wno-tautological-compare -x c++"
)

add_custom_command(
   OUTPUT 
     ${CMAKE_CURRENT_SOURCE_DIR}/btor/btorParser.h
     ${CMAKE_CURRENT_SOURCE_DIR}/btor/btorParser.c
     ${CMAKE_CURRENT_SOURCE_DIR}/btor/btorLexer.h
     ${CMAKE_CURRENT_SOURCE_DIR}/btor/btorLexer.c
     ${CMAKE_CURRENT_SOURCE_DIR}/btor/btor.tokens
   COMMAND 
     ${ANTLR} -make -fo ${CMAKE_CURRENT_SOURCE_DIR}/btor/ ${CMAKE_CURRENT_SOURCE_DIR}/btor/btor.g 
   DEPENDS 
     ${CMAKE_CURRENT_SOURCE_DIR}/btor/btor.g libantlr3c-3.4
)

set_source_files_properties(
  btor/btorParser.c btor/btorLexer.c 
  PROPERTIES 
    LANGUAGE CXX
    COMPILE_FLAGS "-Wno-unused-function -Wno-unused-variable -Wno-tautological-compare -x c++"
)

add_library(parser 
  mcmt/mcmtParser.c 
  mcmt/mcmtLexer.c 
  btor/btorParser.c 
  btor/btorLexer.c 
  parser_state.cpp 
  command.cpp 
  parser.cpp
)
