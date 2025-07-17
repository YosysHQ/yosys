

add_library(yosys_frontends_json OBJECT
    jsonparse.cc
)

target_link_libraries(yosys_obj PUBLIC yosys_frontends_json)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_frontends_json>)
