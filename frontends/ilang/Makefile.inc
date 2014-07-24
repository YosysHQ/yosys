
GENFILES += frontends/ilang/parser.tab.cc
GENFILES += frontends/ilang/parser.tab.h
GENFILES += frontends/ilang/parser.output
GENFILES += frontends/ilang/lexer.cc

frontends/ilang/parser.tab.cc: frontends/ilang/parser.y
	$(P) bison -d -r all -b frontends/ilang/parser frontends/ilang/parser.y
	$(Q) mv frontends/ilang/parser.tab.c frontends/ilang/parser.tab.cc

frontends/ilang/parser.tab.h: frontends/ilang/parser.tab.cc

frontends/ilang/lexer.cc: frontends/ilang/lexer.l
	$(P) flex -o frontends/ilang/lexer.cc frontends/ilang/lexer.l

OBJS += frontends/ilang/parser.tab.o frontends/ilang/lexer.o
OBJS += frontends/ilang/ilang_frontend.o

