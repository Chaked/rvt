CXX=g++
CFLAGS=-c -Wall
LDFLAGS=
SOURCES=rv_arrays.cpp rv_array_assume.cpp rv_collect.cpp rv_commands.cpp rv_consts.cpp rv_ctool.cpp rv_dataflow.cpp rv_dbg.cpp rv_decompose.cpp rv_etc.cpp rv_framasum.cpp rv_funcdfs.cpp rv_funcnode.cpp rv_funcpair.cpp rv_gen.cpp rv_genctx.cpp rv_gotoEliminator.cpp rv_graph.cpp rv_indfunc.cpp rv_loops.cpp rv_main.cpp rv_msg.cpp rv_options.cpp rv_parse.cpp rv_propagate.cpp rv_replace.cpp rv_semchecker.cpp rv_summarizer.cpp rv_temps.cpp rv_tkn_gen.cpp rv_traversal.cpp rv_treecomp.cpp rv_typeeqmac.cpp rv_unroller.cpp rv_walk.cpp ctool/src/context.cpp ctool/src/decl.cpp ctool/src/express.cpp ctool/src/location.cpp ctool/src/parseenv.cpp ctool/src/PrintTraversal.cpp ctool/src/project.cpp ctool/src/stemnt.cpp ctool/src/symbol.cpp ctool/src/token.cpp RVArithConverter.cpp RVTextualUnroller.cpp generated/rv_gram.cpp generated/rv_lexer.cpp
OBJECTS=$(patsubst %.cpp, %.o, $(SOURCES))
EXECUTABLE=rvt

all: $(EXECUTABLE)

$(EXECUTABLE): $(OBJECTS)
	$(CXX) $(LDFLAGS) $(OBJECTS) -o $@

%.o: %.cpp
	$(CXX) -I . -I ctool/include -I ctool/include/ctool $(CFLAGS) $< -o $@
