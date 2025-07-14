

add_library(yosys_frontends_liberty OBJECT
    liberty.cc
)

target_link_libraries(yosys PUBLIC yosys_frontends_liberty)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_frontends_liberty>)
