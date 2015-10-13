
OBJS += backends/smt2/smt2.o

ifneq ($(CONFIG),mxe)
ifneq ($(CONFIG),emcc)
TARGETS += yosys-smtbmc

yosys-smtbmc:
	$(P) sed '3 { p; s|.*|sys.path += [os.path.dirname(__file__) + p for p in ["/share/python3", "/../share/yosys/python3"]]|; }' \
			< backends/smt2/smtbmc.py > yosys-smtbmc.new
	$(Q) chmod +x yosys-smtbmc.new
	$(Q) mv yosys-smtbmc.new yosys-smtbmc

$(eval $(call add_share_file,share/python3,backends/smt2/smtio.py))
endif
endif

