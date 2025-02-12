add_library(yosys_backends_verilog INTERFACE)

target_sources(yosys_backends_verilog INTERFACE
    verilog_backend.cc
)

target_link_libraries(yosys PRIVATE yosys_backends_verilog)
