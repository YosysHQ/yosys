
OBJS += frontends/verific/verific.o

ifeq ($(ENABLE_VERIFIC),1)

EXTRA_TARGETS += share/verific

share/verific:
	rm -rf share/verific.new
	mkdir -p share/verific.new
	cp -r $(VERIFIC_DIR)/vhdl_packages/vdbs share/verific.new/vhdl_vdbs_1993
	cp -r $(VERIFIC_DIR)/vhdl_packages/vdbs_2008 share/verific.new/vhdl_vdbs_2008
	mv share/verific.new share/verific

endif

