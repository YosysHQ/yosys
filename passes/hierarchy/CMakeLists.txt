

add_library(yosys_passes_hierarchy OBJECT
    hierarchy.cc
    uniquify.cc
    submod.cc
    keep_hierarchy.cc
)

target_link_libraries(yosys PUBLIC yosys_passes_hierarchy)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_passes_hierarchy>)
