yosys_frontend(verific
  verific.cc
	verific.h
	verificsva.cc
	REQUIRES
		sha1
	PROVIDES
		read
	REQUIRES
		read_verilog
)
# TODO(cmake):
# ifeq ($(ENABLE_VERIFIC_VHDL),1)
# 	$(Q) cp -r $(VERIFIC_DIR)/vhdl_packages/vdbs_1987/. share/verific.new/vhdl_vdbs_1987
# 	$(Q) cp -r $(VERIFIC_DIR)/vhdl_packages/vdbs_1993/. share/verific.new/vhdl_vdbs_1993
# 	$(Q) cp -r $(VERIFIC_DIR)/vhdl_packages/vdbs_2008/. share/verific.new/vhdl_vdbs_2008
# 	$(Q) cp -r $(VERIFIC_DIR)/vhdl_packages/vdbs_2019/. share/verific.new/vhdl_vdbs_2019
# endif
