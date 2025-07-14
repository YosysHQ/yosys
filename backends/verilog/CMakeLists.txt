

add_library(yosys_backends_verilog OBJECT
    verilog_backend.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_verilog)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_backends_verilog>)
