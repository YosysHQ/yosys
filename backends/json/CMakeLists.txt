

add_library(yosys_backends_json OBJECT
    json.cc
)

target_link_libraries(yosys_obj PUBLIC yosys_backends_json)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_backends_json>)
