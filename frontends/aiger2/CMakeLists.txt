

add_library(yosys_frontends_aiger2 OBJECT
    xaiger.cc
)

target_link_libraries(yosys PUBLIC yosys_frontends_aiger2)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_frontends_aiger2>)
