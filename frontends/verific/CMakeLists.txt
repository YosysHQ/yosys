add_library(yosys_frontends_aiger INTERFACE)

target_sources(yosys_frontends_aiger INTERFACE
    aigerparse.cc
    aigerparse.h
)

target_link_libraries(yosys PRIVATE yosys_frontends_aiger)
