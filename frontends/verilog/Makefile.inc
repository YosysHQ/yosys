
GENFILES += frontends/verilog/verilog_parser.tab.cc
GENFILES += frontends/verilog/verilog_parser.tab.h
GENFILES += frontends/verilog/verilog_parser.output
GENFILES += frontends/verilog/verilog_lexer.cc

frontends/verilog/verilog_parser.tab.cc: frontends/verilog/verilog_parser.y
	$(P) bison -d -r all -b frontends/verilog/verilog_parser frontends/verilog/verilog_parser.y
	$(Q) mv frontends/verilog/verilog_parser.tab.c frontends/verilog/verilog_parser.tab.cc

frontends/verilog/verilog_parser.tab.h: frontends/verilog/verilog_parser.tab.cc

frontends/verilog/verilog_lexer.cc: frontends/verilog/verilog_lexer.l
	$(P) flex -o frontends/verilog/verilog_lexer.cc frontends/verilog/verilog_lexer.l

OBJS += frontends/verilog/verilog_parser.tab.o
OBJS += frontends/verilog/verilog_lexer.o
OBJS += frontends/verilog/preproc.o
OBJS += frontends/verilog/verilog_frontend.o
OBJS += frontends/verilog/const2ast.o

