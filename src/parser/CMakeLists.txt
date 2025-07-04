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
    COMPILE_FLAGS "-Wno-parentheses-equality -Wno-sign-compare -Wno-unused-function -Wno-unused-variable -Wno-tautological-compare -x c++"
)

add_custom_command(
   OUTPUT 
     ${CMAKE_CURRENT_SOURCE_DIR}/smt2/smt2Parser.h
     ${CMAKE_CURRENT_SOURCE_DIR}/smt2/smt2Parser.c
     ${CMAKE_CURRENT_SOURCE_DIR}/smt2/smt2Lexer.h
     ${CMAKE_CURRENT_SOURCE_DIR}/smt2/smt2Lexer.c
     ${CMAKE_CURRENT_SOURCE_DIR}/smt2/smt2.tokens
   COMMAND 
     ${ANTLR} -make -fo ${CMAKE_CURRENT_SOURCE_DIR}/smt2/ ${CMAKE_CURRENT_SOURCE_DIR}/smt2/smt2.g 
   DEPENDS 
     ${CMAKE_CURRENT_SOURCE_DIR}/smt2/smt2.g libantlr3c-3.4
)

set_source_files_properties(
  smt2/smt2Parser.c smt2/smt2Lexer.c 
  PROPERTIES 
    LANGUAGE CXX
    COMPILE_FLAGS "-Wno-parentheses-equality -Wno-sign-compare -Wno-unused-function -Wno-unused-variable -Wno-tautological-compare -x c++"
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
    COMPILE_FLAGS "-Wno-parentheses-equality -Wno-sign-compare -Wno-unused-function -Wno-unused-variable -Wno-tautological-compare -x c++"
)

add_custom_command(
   OUTPUT 
     ${CMAKE_CURRENT_SOURCE_DIR}/sal/salParser.h
     ${CMAKE_CURRENT_SOURCE_DIR}/sal/salParser.c
     ${CMAKE_CURRENT_SOURCE_DIR}/sal/salLexer.h
     ${CMAKE_CURRENT_SOURCE_DIR}/sal/salLexer.c
     ${CMAKE_CURRENT_SOURCE_DIR}/sal/sal.tokens
   COMMAND 
     ${ANTLR} -make -fo ${CMAKE_CURRENT_SOURCE_DIR}/sal/ ${CMAKE_CURRENT_SOURCE_DIR}/sal/sal.g 
   DEPENDS 
     ${CMAKE_CURRENT_SOURCE_DIR}/sal/sal.g libantlr3c-3.4
)

set_source_files_properties(
  sal/salParser.c sal/salLexer.c 
  PROPERTIES 
    LANGUAGE CXX
    COMPILE_FLAGS "-Wno-parentheses-equality -Wno-sign-compare -Wno-unused-function -Wno-unused-variable -Wno-tautological-compare -x c++"
)

set_source_files_properties(
  aiger/aiger-1.9.4/aiger.c
  PROPERTIES
    LANGUAGE C
)

add_library(parser 
  mcmt/mcmtParser.c 
  mcmt/mcmtLexer.c 
  mcmt/mcmt_state.cpp
  mcmt/mcmt.cpp
  smt2/smt2Parser.c
  smt2/smt2Lexer.c
  smt2/smt2_state.cpp
  smt2/smt2.cpp
  btor/btorParser.c 
  btor/btorLexer.c 
  btor/btor_state.cpp
  btor/btor.cpp
  btor2/btor2.cpp
  sal/salParser.c 
  sal/salLexer.c 
  sal/sal_state.cpp
  sal/sal_context.cpp
  sal/sal_module.cpp
  sal/sal.cpp
  aiger/aiger.cpp
  aiger/aiger-1.9.4/aiger.c
  parser.cpp
)
