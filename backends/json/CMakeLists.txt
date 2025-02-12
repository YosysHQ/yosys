add_library(yosys_backends_json INTERFACE)

target_sources(yosys_backends_json INTERFACE
    json.cc
)

target_link_libraries(yosys PRIVATE yosys_backends_json)
