add_library(yosys_passes_hierarchy INTERFACE)

target_sources(yosys_passes_hierarchy INTERFACE
    hierarchy.cc
    uniquify.cc
    submod.cc
    keep_hierarchy.cc
)

target_link_libraries(yosys PRIVATE yosys_passes_hierarchy)
