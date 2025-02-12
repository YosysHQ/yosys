add_library(yosys_frontends_blif INTERFACE)

target_sources(yosys_frontends_blif INTERFACE
    blifparse.cc
    blifparse.h
)

target_link_libraries(yosys PRIVATE yosys_frontends_blif)
