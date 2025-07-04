add_library(yosys_backends_cxxrtl INTERFACE)

target_sources(yosys_backends_cxxrtl INTERFACE
    cxxrtl_backend.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_cxxrtl)

add_include_file("backends/cxxrtl/runtime/cxxrtl" "runtime/cxxrtl/cxxrtl.h")
add_include_file("backends/cxxrtl/runtime/cxxrtl" "runtime/cxxrtl/cxxrtl_vcd.h")
add_include_file("backends/cxxrtl/runtime/cxxrtl" "runtime/cxxrtl/cxxrtl_time.h")
add_include_file("backends/cxxrtl/runtime/cxxrtl" "runtime/cxxrtl/cxxrtl_replay.h")
add_include_file("backends/cxxrtl/runtime/cxxrtl/capi" "runtime/cxxrtl/capi/cxxrtl_capi.cc")
add_include_file("backends/cxxrtl/runtime/cxxrtl/capi" "runtime/cxxrtl/capi/cxxrtl_capi.h")
add_include_file("backends/cxxrtl/runtime/cxxrtl/capi" "runtime/cxxrtl/capi/cxxrtl_capi_vcd.cc")
add_include_file("backends/cxxrtl/runtime/cxxrtl/capi" "runtime/cxxrtl/capi/cxxrtl_capi_vcd.h")
