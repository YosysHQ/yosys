add_library(yosys_techlibs_fabulous INTERFACE)

target_sources(yosys_techlibs_fabulous INTERFACE
    synth_fabulous.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_fabulous)
