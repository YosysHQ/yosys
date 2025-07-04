add_library(yosys_backends_verilog INTERFACE)

target_sources(yosys_backends_verilog INTERFACE
    verilog_backend.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_verilog)
