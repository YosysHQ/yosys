add_library(yosys_backends_firrtl INTERFACE)

target_sources(yosys_backends_firrtl INTERFACE
    firrtl.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_firrtl)
