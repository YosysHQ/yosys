
GENFILES += frontends/verilog/verilog_parser.tab.cc
GENFILES += frontends/verilog/verilog_parser.tab.hh
GENFILES += frontends/verilog/verilog_parser.output
GENFILES += frontends/verilog/verilog_lexer.cc

frontends/verilog/verilog_parser.tab.cc: frontends/verilog/verilog_parser.y
	$(Q) mkdir -p $(dir $@)
	$(P) $(BISON) -o $@ -d -r all -b frontends/verilog/verilog_parser $<

frontends/verilog/verilog_parser.tab.hh: frontends/verilog/verilog_parser.tab.cc

frontends/verilog/verilog_lexer.cc: frontends/verilog/verilog_lexer.l
	$(Q) mkdir -p $(dir $@)
	$(P) flex -o frontends/verilog/verilog_lexer.cc $<

frontends/verilog/verilog_parser.tab.o: CXXFLAGS += -DYYMAXDEPTH=10000000

OBJS += frontends/verilog/verilog_parser.tab.o
OBJS += frontends/verilog/verilog_lexer.o
OBJS += frontends/verilog/preproc.o
OBJS += frontends/verilog/verilog_frontend.o
OBJS += frontends/verilog/const2ast.o

