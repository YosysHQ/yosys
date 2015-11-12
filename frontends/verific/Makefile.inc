
OBJS += frontends/verific/verific.o

ifeq ($(ENABLE_VERIFIC),1)

EXTRA_TARGETS += share/verific

share/verific:
	$(P) rm -rf share/verific.new
	$(Q) mkdir -p share/verific.new
	$(Q) cp -r $(VERIFIC_DIR)/vhdl_packages/vdbs_1987/. share/verific.new/vhdl_vdbs_1987
	$(Q) cp -r $(VERIFIC_DIR)/vhdl_packages/vdbs_1993/. share/verific.new/vhdl_vdbs_1993
	$(Q) cp -r $(VERIFIC_DIR)/vhdl_packages/vdbs_2008/. share/verific.new/vhdl_vdbs_2008
	$(Q) mv share/verific.new share/verific

endif

