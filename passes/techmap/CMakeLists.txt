add_library(yosys_passes_techmap INTERFACE)

target_sources(yosys_passes_techmap INTERFACE
    libparse.cc
)

target_link_libraries(yosys PRIVATE yosys_passes_techmap)
