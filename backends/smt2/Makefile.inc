
OBJS += backends/smt2/smt2.o

ifneq ($(CONFIG),mxe)
ifneq ($(CONFIG),emcc)
TARGETS += yosys-smtbmc

yosys-smtbmc: backends/smt2/smtbmc.py
	$(P) sed 's|##yosys-sys-path##|sys.path += [os.path.dirname(__file__) + p for p in ["/share/python3", "/../share/yosys/python3"]]|;' < $< > $@.new
	$(Q) chmod +x $@.new
	$(Q) mv $@.new $@

$(eval $(call add_share_file,share/python3,backends/smt2/smtio.py))
endif
endif

