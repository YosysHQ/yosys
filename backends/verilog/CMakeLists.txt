

add_library(yosys_backends_verilog OBJECT
    verilog_backend.cc
)

target_link_libraries(yosys_obj PUBLIC yosys_backends_verilog)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_backends_verilog>)
