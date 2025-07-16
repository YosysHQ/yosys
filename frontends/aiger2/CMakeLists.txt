

add_library(yosys_frontends_aiger2 OBJECT
    xaiger.cc
)

target_link_libraries(yosys_obj PUBLIC yosys_frontends_aiger2)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_frontends_aiger2>)
