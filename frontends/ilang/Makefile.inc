
GENFILES += frontends/ilang/ilang_parser.tab.cc
GENFILES += frontends/ilang/ilang_parser.tab.h
GENFILES += frontends/ilang/ilang_parser.output
GENFILES += frontends/ilang/ilang_lexer.cc

frontends/ilang/ilang_parser.tab.cc: frontends/ilang/ilang_parser.y
	$(P) bison -d -r all -b frontends/ilang/ilang_parser frontends/ilang/ilang_parser.y
	$(Q) mv frontends/ilang/ilang_parser.tab.c frontends/ilang/ilang_parser.tab.cc

frontends/ilang/ilang_parser.tab.h: frontends/ilang/ilang_parser.tab.cc

frontends/ilang/ilang_lexer.cc: frontends/ilang/ilang_lexer.l
	$(P) flex -o frontends/ilang/ilang_lexer.cc frontends/ilang/ilang_lexer.l

OBJS += frontends/ilang/ilang_parser.tab.o frontends/ilang/ilang_lexer.o
OBJS += frontends/ilang/ilang_frontend.o

