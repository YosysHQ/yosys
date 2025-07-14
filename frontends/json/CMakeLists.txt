

add_library(yosys_frontends_json OBJECT
    jsonparse.cc
)

target_link_libraries(yosys PUBLIC yosys_frontends_json)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_frontends_json>)
