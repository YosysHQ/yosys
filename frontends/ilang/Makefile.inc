
GENFILES += frontends/ilang/ilang_parser.tab.cc
GENFILES += frontends/ilang/ilang_parser.tab.h
GENFILES += frontends/ilang/ilang_parser.output
GENFILES += frontends/ilang/ilang_lexer.cc

frontends/ilang/ilang_parser.tab.cc: frontends/ilang/ilang_parser.y
	$(Q) mkdir -p $(dir $@)
	$(P) $(BISON) -d -r all -b frontends/ilang/ilang_parser $<
	$(Q) mv frontends/ilang/ilang_parser.tab.c frontends/ilang/ilang_parser.tab.cc

frontends/ilang/ilang_parser.tab.h: frontends/ilang/ilang_parser.tab.cc

frontends/ilang/ilang_lexer.cc: frontends/ilang/ilang_lexer.l
	$(Q) mkdir -p $(dir $@)
	$(P) flex -o frontends/ilang/ilang_lexer.cc $<

OBJS += frontends/ilang/ilang_parser.tab.o frontends/ilang/ilang_lexer.o
OBJS += frontends/ilang/ilang_frontend.o

