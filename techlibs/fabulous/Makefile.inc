
OBJS += techlibs/fabulous/synth_fabulous.o

$(eval $(call add_share_file,share/fabulous,techlibs/fabulous/cells_map.v))
$(eval $(call add_share_file,share/fabulous,techlibs/fabulous/prims.v))
$(eval $(call add_share_file,share/fabulous,techlibs/fabulous/latches_map.v))
$(eval $(call add_share_file,share/fabulous,techlibs/fabulous/ff_map.v))
$(eval $(call add_share_file,share/fabulous,techlibs/fabulous/ram_regfile.txt))
$(eval $(call add_share_file,share/fabulous,techlibs/fabulous/regfile_map.v))
$(eval $(call add_share_file,share/fabulous,techlibs/fabulous/io_map.v))
