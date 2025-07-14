

add_library(yosys_backends_json OBJECT
    json.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_json)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_backends_json>)
