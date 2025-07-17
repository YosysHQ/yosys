

add_library(yosys_frontends_liberty OBJECT
    liberty.cc
)

target_link_libraries(yosys_obj PUBLIC yosys_frontends_liberty)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_frontends_liberty>)
