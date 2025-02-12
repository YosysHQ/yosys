add_library(yosys_frontends_aiger2 INTERFACE)

target_sources(yosys_frontends_aiger2 INTERFACE
    xaiger.cc
)

target_link_libraries(yosys PRIVATE yosys_frontends_aiger2)
