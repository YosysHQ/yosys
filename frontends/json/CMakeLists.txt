add_library(yosys_frontends_json INTERFACE)

target_sources(yosys_frontends_json INTERFACE
    jsonparse.cc
)

target_link_libraries(yosys PRIVATE yosys_frontends_json)
