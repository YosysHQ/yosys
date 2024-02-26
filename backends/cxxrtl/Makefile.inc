
OBJS += backends/cxxrtl/cxxrtl_backend.o

$(eval $(call add_include_file,backends/cxxrtl/runtime/cxxrtl/cxxrtl.h))
$(eval $(call add_include_file,backends/cxxrtl/runtime/cxxrtl/cxxrtl_vcd.h))
$(eval $(call add_include_file,backends/cxxrtl/runtime/cxxrtl/cxxrtl_time.h))
$(eval $(call add_include_file,backends/cxxrtl/runtime/cxxrtl/cxxrtl_replay.h))
$(eval $(call add_include_file,backends/cxxrtl/runtime/cxxrtl/capi/cxxrtl_capi.cc))
$(eval $(call add_include_file,backends/cxxrtl/runtime/cxxrtl/capi/cxxrtl_capi.h))
$(eval $(call add_include_file,backends/cxxrtl/runtime/cxxrtl/capi/cxxrtl_capi_vcd.cc))
$(eval $(call add_include_file,backends/cxxrtl/runtime/cxxrtl/capi/cxxrtl_capi_vcd.h))
