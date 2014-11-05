add_custom_command(
   OUTPUT 
     ${CMAKE_CURRENT_SOURCE_DIR}/mcmtParser.h
     ${CMAKE_CURRENT_SOURCE_DIR}/mcmtParser.c
     ${CMAKE_CURRENT_SOURCE_DIR}/mcmtLexer.h
     ${CMAKE_CURRENT_SOURCE_DIR}/mcmtLexer.c
     ${CMAKE_CURRENT_SOURCE_DIR}/mcmt.tokens
   COMMAND 
     ${ANTLR} -fo ${CMAKE_CURRENT_SOURCE_DIR} ${CMAKE_CURRENT_SOURCE_DIR}/mcmt.g 
   DEPENDS 
     ${CMAKE_CURRENT_SOURCE_DIR}/mcmt.g
)

add_library(parser parser.cpp mcmtParser.c mcmtLexer.c)

