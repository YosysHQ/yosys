
GENFILES += frontends/rtlil/rtlil_parser.tab.cc
GENFILES += frontends/rtlil/rtlil_parser.tab.hh
GENFILES += frontends/rtlil/rtlil_parser.output
GENFILES += frontends/rtlil/rtlil_lexer.cc

frontends/rtlil/rtlil_parser.tab.cc: frontends/rtlil/rtlil_parser.y
	$(Q) mkdir -p $(dir $@)
	$(P) $(BISON) -o $@ -d -r all -b frontends/rtlil/rtlil_parser $<

frontends/rtlil/rtlil_parser.tab.hh: frontends/rtlil/rtlil_parser.tab.cc

frontends/rtlil/rtlil_lexer.cc: frontends/rtlil/rtlil_lexer.l
	$(Q) mkdir -p $(dir $@)
	$(P) flex -o frontends/rtlil/rtlil_lexer.cc $<

OBJS += frontends/rtlil/rtlil_parser.tab.o frontends/rtlil/rtlil_lexer.o
OBJS += frontends/rtlil/rtlil_frontend.o

