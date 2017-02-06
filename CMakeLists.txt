cmake_minimum_required (VERSION 3.3)
project (rvt)

set(CMAKE_CXX_STANDARD 11)

find_package(BISON REQUIRED)
find_package(FLEX REQUIRED)

include_directories(
  ${PROJECT_SOURCE_DIR}
  ${PROJECT_SOURCE_DIR}/ctool/include)

BISON_TARGET(rv_gram
  ${PROJECT_SOURCE_DIR}/rv_gram.y
  ${CMAKE_CURRENT_BINARY_DIR}/rv_gram.cpp)
FLEX_TARGET(rv_lexer ${PROJECT_SOURCE_DIR}/rv_lexer.l  ${CMAKE_CURRENT_BINARY_DIR}/rv_lexer.cpp)
ADD_FLEX_BISON_DEPENDENCY(rv_lexer rv_gram)

add_executable(rvt
  rv_arrays.cpp
  rv_array_assume.cpp
  rv_collect.cpp
  rv_commands.cpp
  rv_consts.cpp
  rv_ctool.cpp
  rv_dataflow.cpp
  rv_dbg.cpp
  rv_decompose.cpp
  rv_etc.cpp
  rv_framasum.cpp
  rv_funcdfs.cpp
  rv_funcnode.cpp
  rv_funcpair.cpp
  rv_gen.cpp
  rv_genctx.cpp
  rv_gotoEliminator.cpp
  rv_graph.cpp
  rv_indfunc.cpp
  rv_loops.cpp
  rv_main.cpp
  rv_msg.cpp
  rv_options.cpp
  rv_parse.cpp
  rv_propagate.cpp
  rv_replace.cpp
  rv_semchecker.cpp
  rv_summarizer.cpp
  rv_temps.cpp
  rv_tkn_gen.cpp
  rv_traversal.cpp
  rv_treecomp.cpp
  rv_typeeqmac.cpp
  rv_unroller.cpp
  rv_walk.cpp
  ctool/src/context.cpp
  ctool/src/decl.cpp
  ctool/src/express.cpp
  ctool/src/location.cpp
  ctool/src/parseenv.cpp
  ctool/src/PrintTraversal.cpp
  ctool/src/project.cpp
  ctool/src/stemnt.cpp
  ctool/src/symbol.cpp
  ctool/src/token.cpp
  RVArithConverter.cpp
  RVTextualUnroller.cpp
  ${FLEX_rv_lexer_OUTPUTS}
  ${BISON_rv_gram_OUTPUTS})
