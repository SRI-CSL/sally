add_custom_command(
   OUTPUT 
     mcmtParser.h
     mcmtParser.c
     mcmtLexer.h
     mcmtLexer.c
     mcmt.tokens
   COMMAND 
     ${ANTLR} -fo ${CMAKE_CURRENT_SOURCE_DIR} ${CMAKE_CURRENT_SOURCE_DIR}/mcmt.g 
   DEPENDS 
     ${CMAKE_CURRENT_SOURCE_DIR}/mcmt.g
)

add_library(parser parser.cpp mcmtParser.c mcmtLexer.c)
