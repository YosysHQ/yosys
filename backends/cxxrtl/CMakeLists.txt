add_library(yosys_backends_cxxrtl INTERFACE)

target_sources(yosys_backends_cxxrtl INTERFACE
    cxxrtl_backend.cc
)

target_link_libraries(yosys PRIVATE yosys_backends_cxxrtl)
