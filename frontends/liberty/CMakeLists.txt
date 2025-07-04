add_library(yosys_frontends_liberty INTERFACE)

target_sources(yosys_frontends_liberty INTERFACE
    liberty.cc
)

target_link_libraries(yosys PUBLIC yosys_frontends_liberty)
