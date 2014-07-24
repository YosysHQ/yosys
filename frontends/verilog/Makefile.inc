
GENFILES += frontends/verilog/parser.tab.cc
GENFILES += frontends/verilog/parser.tab.h
GENFILES += frontends/verilog/parser.output
GENFILES += frontends/verilog/lexer.cc

frontends/verilog/parser.tab.cc: frontends/verilog/parser.y
	$(P) bison -d -r all -b frontends/verilog/parser frontends/verilog/parser.y
	$(Q) mv frontends/verilog/parser.tab.c frontends/verilog/parser.tab.cc

frontends/verilog/parser.tab.h: frontends/verilog/parser.tab.cc

frontends/verilog/lexer.cc: frontends/verilog/lexer.l
	$(P) flex -o frontends/verilog/lexer.cc frontends/verilog/lexer.l

OBJS += frontends/verilog/parser.tab.o
OBJS += frontends/verilog/lexer.o
OBJS += frontends/verilog/preproc.o
OBJS += frontends/verilog/verilog_frontend.o
OBJS += frontends/verilog/const2ast.o

