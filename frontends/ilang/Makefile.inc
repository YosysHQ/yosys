
GENFILES += frontends/ilang/ilang_parser.tab.cc
GENFILES += frontends/ilang/ilang_parser.tab.hh
GENFILES += frontends/ilang/ilang_parser.output
GENFILES += frontends/ilang/ilang_lexer.cc

frontends/ilang/ilang_parser.tab.cc: frontends/ilang/ilang_parser.y
	$(Q) mkdir -p $(dir $@)
	$(P) $(BISON) -o $@ -d -r all -b frontends/ilang/ilang_parser $<

frontends/ilang/ilang_parser.tab.hh: frontends/ilang/ilang_parser.tab.cc

frontends/ilang/ilang_lexer.cc: frontends/ilang/ilang_lexer.l
	$(Q) mkdir -p $(dir $@)
	$(P) flex -o frontends/ilang/ilang_lexer.cc $<

OBJS += frontends/ilang/ilang_parser.tab.o frontends/ilang/ilang_lexer.o
OBJS += frontends/ilang/ilang_frontend.o

